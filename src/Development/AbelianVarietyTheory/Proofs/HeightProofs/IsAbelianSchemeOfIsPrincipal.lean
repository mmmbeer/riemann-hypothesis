import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.EigenLatticeFibres
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralTangentVectorCoordinates
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOfCmTriplePullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenySumOfCmHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CommutatorPairingsEqOfCubeLBPairingIso
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory.CM GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section
namespace GlobalTheory.CMSharedCompare

section Comb

variable {R : Type} [CommRing R]

theorem comb_transfer {S : Scheme.{0}} {G : Over S} {A A' : Over (Sp R)} [GrpObj G] [GrpObj A] [GrpObj A']
    {f : Sp R ⟶ S} {φ : A.left ⟶ G.left} {φ' : A'.left ⟶ G.left} (h : IsGrpPullback A G f φ)
    (h' : IsGrpPullback A' G f φ') {n : ℕ} {v : Fin n → (epsR R ⟶ A)} {v' : Fin n → (epsR R ⟶ A')}
    (e : ∀ i, (v' i).left ≫ φ' = (v i).left ≫ φ) {c : Fin n → R} {w : epsR R ⟶ A} (hw : IsLieComb c v w) :
    ∃ w', IsLieComb c v' w' ∧ w'.left ≫ φ' = w.left ≫ φ := by
  obtain ⟨i, hi, hφ⟩ := grpPullback_iso h h'
  have : v' = fun j => v j ≫ i.hom := funext fun j => Over.OverMorphism.ext
    (h'.1.hom_ext (by rw [e, Over.comp_left, Category.assoc, hφ]) ((Over.w _).trans (Over.w _).symm))
  subst this
  exact ⟨w ≫ i.hom, DiffCoord.isLieComb_comp_hom i.hom hw, by rw [Over.comp_left, Category.assoc, hφ]⟩

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]

section Vec

variable {t : SAB H (Sp (𝓞 K))} (G : EigenLatticeFibres.GenFib t)

theorem coord_unique {c c' : Fin G.g → K} {x : Sp (DualNumber K) ⟶ t.G.left} (h : G.IsVec c x) (h' : G.IsVec c' x) :
    c = c' := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨w', hw', e⟩ := h'
  obtain rfl : w = w' := Over.OverMorphism.ext (G.m.cart.1.hom_ext e ((Over.w _).trans (Over.w _).symm))
  exact (G.basis.2 w ((LieComb.lieComb_algebra K _ _ G.v G.basis.1).2.1 c w hw)).unique hw hw'

end Vec

structure Partner {T : PAT H (Sp (𝓞 K))} (F : GenFib T.pol) where

  tK : SAB H (Sp K)

  m : SABMap tK T.t (spMap (algebraMap (𝓞 K) K))

  v : Fin F.P₀.g → (epsR K ⟶ tK.G)
  basis : IsLieBasis v
  same : ∀ i, (v i).left ≫ m.φ = (F.v i).left ≫ F.φ

variable {T T' : PAT H (Sp (𝓞 K))}

namespace Partner

variable {F : GenFib T.pol} {F' : GenFib T'.pol} (Q : Partner F) (Q' : Partner F')

end Partner

section Metric

variable {T : PAT H (Sp (𝓞 K))} {F : GenFib T.pol} (Q : Partner F)

end Metric

section Embeddings

theorem injective_of_charZero {k : Type} [CommRing k] [CharZero k] (β : 𝓞 K →+* k) : Function.Injective β := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => ?_)
  simpa [RingHom.mem_ker] using hn

theorem mapRingHom_bijective (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] :
    Function.Bijective (RingOfIntegers.mapRingHom : (E →+* K) → (𝓞 E →+* 𝓞 K)) := by
  refine ⟨fun f g e => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_), fun τ => ?_⟩
  · exact congrArg (fun x : 𝓞 E →+* 𝓞 K => (x a : K)) e
  · have hi := injective_of_charZero ((algebraMap (𝓞 K) K).comp τ)
    exact ⟨IsFractionRing.lift hi, RingHom.ext fun a => Subtype.ext (IsFractionRing.lift_algebraMap hi a)⟩

theorem splits_iff (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] :
    Splits E K ↔ EigenLatticeFibres.SplitsE E K := by
  rw [Splits, EigenLatticeFibres.SplitsE, Nat.card_eq_of_bijective _ (mapRingHom_bijective E K)]

theorem hasSig_iff {G : Over (Sp (𝓞 K))} [GrpObj G] (act : OAct (𝓞 E) G) (ρ : 𝓞 K) (p q : ℕ) :
    CMCurveHermitianForms.HasSig H p q act ρ ↔ ρ ^ 2 = -(H.d : 𝓞 K) ∧ HasType H act ρ p q :=
  and_congr_right fun _ => ⟨fun h k _ _ β hβ =>
    have : CharZero k := charZero_of_injective_ringHom hβ
    h k β, fun h k _ _ _ β => h k β (injective_of_charZero β)⟩

end Embeddings

section Isogeny

theorem isFinFlatSurj_of_onto (σ : K →+* ℂ) (P P' : Out.PolAV (Sp (𝓞 K))) (Φ : P.A ⟶ P'.A) (hg : P.g = P'.g)
    [hΦ : IsMonHom Φ] (h : ∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P'.A,
      ∃ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, y = x ≫ Φ) : EigenLatticeFibres.IsFinFlatSurj Φ := by
  have hL := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have hs := (OntoSurj.surjective_of_onto_complex_points _ _ (injective_of_charZero _) _ _ Φ P'.isAb P.isAb h).1
  obtain ⟨N, ψ, hN, -, h₁, -⟩ := LamF.exists_inverse_isogeny_ringOfIntegers thetaUnifAV_all hL
    homExtension_semiAbelian_dvr_unconditional K σ P P' Φ hg hΦ h
  have := P.isAb.proper
  have := P'.isAb.proper
  have := P.isAb.smooth
  have := P.isAb.comm
  have : IsSeparated ψ.left := by
    have : IsSeparated (ψ.left ≫ P.A.hom) := by rw [Over.w]; infer_instance
    exact IsSeparated.of_comp ψ.left P.A.hom
  have hf : IsFinite Φ.left := by
    have : IsFinite (Φ.left ≫ ψ.left) := by
      rw [← Over.comp_left, h₁]
      exact (hL.mulN _ P N hN).1
    exact IsFinite.of_comp Φ.left ψ.left
  refine ⟨hf, flat_of_isFinite_of_flat_geometric_fibres _ _ _ Φ inferInstance inferInstance hf fun k _ _ t => ?_, hs⟩
  refine (isogeny_of_surjective_of_dim_eq hL k
    (TorsionTauCompare.polOfPullback P _ (isGrpPullback_pullback P.A t)) _ ((Over.pullback t).map Φ)
    (PolPull.isAbelianScheme_of_isGrpPullback P'.isAb (isGrpPullback_pullback P'.A t)) ?_
    (inferInstanceAs (IsMonHom ((Over.pullback t).map Φ)))
    (MorphismProperty.of_isPullback (P := @Surjective) (AbLaw.MulN.isPullback_baseChange t Φ) hs)).2.1
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (isGrpPullback_pullback P'.A t).1
    (hg ▸ P'.smoothDim)

theorem comp_sumMap {S : Scheme.{0}} {A A' B Z : Over S} [GrpObj B] [IsCommMonObj B] {p q : ℕ} (f : Fin p → (A ⟶ B))
    (f' : Fin q → (A' ⟶ B)) (x : Z ⟶ (∏ᶜ fun _ : Fin p => A) ⊗ (∏ᶜ fun _ : Fin q => A')) :
    x ≫ EigenLatticeFibres.sumMap f f' = (∏ i, (x ≫ fst _ _ ≫ Pi.π _ i) ≫ f i) * ∏ j, (x ≫ snd _ _ ≫ Pi.π _ j) ≫ f' j := by
  simp only [EigenLatticeFibres.sumMap, EigenLatticeFibres.sumPow, List.prod_ofFn, MonObj.comp_mul, LamF.IsogSum.comp_prod, Category.assoc]

theorem isFinFlatSurj_sumMap_iff (σ : K →+* ℂ) (A A' B : Out.PolAV (Sp (𝓞 K))) [IsCommMonObj B.A] {p q : ℕ}
    (f : Fin p → (A.A ⟶ B.A)) (f' : Fin q → (A'.A ⟶ B.A)) (hf : ∀ i, IsMonHom (f i)) (hf' : ∀ i, IsMonHom (f' i))
    (hg : B.g = p * A.g + q * A'.g) :
    EigenLatticeFibres.IsFinFlatSurj (EigenLatticeFibres.sumMap f f') ↔ ∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.A,
      ∃ (x : Fin p → (_ ⟶ A.A)) (x' : Fin q → (_ ⟶ A'.A)), y = (∏ i, x i ≫ f i) * ∏ j, x' j ≫ f' j := by
  constructor
  · rintro ⟨h₁, -, h₃⟩ y
    obtain ⟨z, hz⟩ := GeomSurj.exists_lift_of_surjective (EigenLatticeFibres.sumMap f f').left y.left
    let x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (∏ᶜ fun _ : Fin p => A.A) ⊗ (∏ᶜ fun _ : Fin q => A'.A) :=
      Over.homMk z (by rw [← Over.w (EigenLatticeFibres.sumMap f f'), ← Category.assoc, ← hz]; exact Over.w y)
    exact ⟨_, _, (Over.OverMorphism.ext hz : y = x ≫ _).trans (comp_sumMap f f' x)⟩
  · intro hs
    obtain ⟨P, pP, hP⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) A p
    obtain ⟨P', pP', hP'⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power (𝓞 K) A' q
    obtain ⟨Q, u, v, hu, hv, huv, hQ⟩ := GlobalTheory.T.exists_prod_polAV_add_g GlobalTheory.T.abelianScheme_laws_unconditional.1 (𝓞 K) P P'
    have := pP.hom
    have := pP'.hom
    have := Q.isAb.comm
    have := A.isAb.comm
    have := A'.isAb.comm
    let a := pP.lim.conePointUniqueUpToIso (productIsProduct fun _ : Fin p => A.A)
    let b := pP'.lim.conePointUniqueUpToIso (productIsProduct fun _ : Fin q => A'.A)
    have ha : ∀ i, a.hom ≫ Pi.π _ i = pP.pr i := fun i =>
      pP.lim.conePointUniqueUpToIso_hom_comp (productIsProduct fun _ : Fin p => A.A) ⟨i⟩
    have hb : ∀ i, b.hom ≫ Pi.π _ i = pP'.pr i := fun i =>
      pP'.lim.conePointUniqueUpToIso_hom_comp (productIsProduct fun _ : Fin q => A'.A) ⟨i⟩
    let e : Q.A ≅ (∏ᶜ fun _ : Fin p => A.A) ⊗ (∏ᶜ fun _ : Fin q => A'.A) := asIso (lift u v) ≪≫ (a ⊗ᵢ b)
    have e₁ : e.hom ≫ fst _ _ = u ≫ a.hom := by simp [e]
    have e₂ : e.hom ≫ snd _ _ = v ≫ b.hom := by simp [e]
    have hΦ : ∀ {Z : Over (Sp (𝓞 K))} (x : Z ⟶ Q.A), x ≫ e.hom ≫ EigenLatticeFibres.sumMap f f' =
        (∏ i, (x ≫ u ≫ pP.pr i) ≫ f i) * ∏ i, (x ≫ v ≫ pP'.pr i) ≫ f' i := fun x => by
      rw [← Category.assoc, comp_sumMap]
      simp only [Category.assoc, reassoc_of% e₁, reassoc_of% e₂, ← ha, ← hb]
    have hm : IsMonHom (e.hom ≫ EigenLatticeFibres.sumMap f f') := LamF.IsogSum.isMonHom_of_points _ fun Z x y => by
      simp only [hΦ, MonObj.mul_comp, Finset.prod_mul_distrib]
      exact mul_mul_mul_comm _ _ _ _
    obtain ⟨h₁, h₂, h₃⟩ := isFinFlatSurj_of_onto σ Q B (e.hom ≫ EigenLatticeFibres.sumMap f f') (by rw [hQ, hP, hP', hg])
      fun y => by
        obtain ⟨x, x', hx⟩ := hs y
        obtain ⟨z, hz, hz'⟩ := LamF.IsogSum.exists_point pP pP' u v x x'
        exact ⟨z, by rw [hΦ, hx]; simp only [hz, hz']⟩
    have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
    have he : (EigenLatticeFibres.sumMap f f').left = e.inv.left ≫ (e.hom ≫ EigenLatticeFibres.sumMap f f').left := by
      rw [← Over.comp_left, e.inv_hom_id_assoc]
    unfold EigenLatticeFibres.IsFinFlatSurj
    rw [he]
    exact ⟨inferInstance, inferInstance, inferInstance⟩

end Isogeny

section Object

theorem polId_iff (σ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f : A.t.G ⟶ B.t.G) (hf : IsMonHom f) (h : 𝓞 E) :
    EigenLatticeFibres.PolId f h ↔ WeilEq B.t.PP.L f f A.t.PP.L (A.t.act.act h) (𝟙 _) (spMap (σ.comp (algebraMap (𝓞 K) K))) := by
  refine ⟨fun w n x y c hn hx hy => w n hn _ x y hx hy (unitOn c), fun w k hk Z x y hx hy c => ?_⟩
  have hL := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have h₁ : IsMonHom (𝟙 A.pol.A) := inferInstance
  exact PairingScheme.weilIs_iff_of_lamEq hL (𝓞 K) A.pol A.pol B.pol A.pol _ _ _ _ hf hf (A.t.act.hom h) h₁
    ((PairingFibre.lamEq_weilEq_over_ring hL (𝓞 K) A.pol A.pol B.pol A.pol _ _ _ _ hf hf (A.t.act.hom h) h₁ ℂ
      (σ.comp (algebraMap (𝓞 K) K))).2 inferInstance (injective_of_charZero _) w) Z k x y c hk hx hy

theorem isLinHom_iff {S : Scheme.{0}} {t t' : SAB H S} (f : t.G ⟶ t'.G) :
    EigenLatticeFibres.IsLinHom f ↔ Serre.IsLinearHom t.act t'.act f :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem isPrincipal {S : Scheme.{0}} (T : PAT H S) : CMCurveHermitianForms.IsPrincipal T.t := ⟨T.ab.proper, T.ample, T.ktriv⟩

theorem isAbelianScheme_of_isPrincipal {S : Scheme.{0}} {t : SAB H S} (h : CMCurveHermitianForms.IsPrincipal t) :
    IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, h.proper, t.semi.geomConnected⟩

theorem exists_dim {t : SAB H (Sp (𝓞 K))} (h : CMCurveHermitianForms.IsPrincipal t) : ∃ g, SmoothOfRelativeDimension g t.G.hom :=
  have : ConnectedSpace (Sp (𝓞 K)) := inferInstanceAs (ConnectedSpace (PrimeSpectrum (𝓞 K)))
  AbelianDim.exists_relDim_of_connected t.G (isAbelianScheme_of_isPrincipal h)

def patOf (t : SAB H (Sp (𝓞 K))) (h : CMCurveHermitianForms.IsPrincipal t) : PAT H (Sp (𝓞 K)) where
  t := t
  ab := isAbelianScheme_of_isPrincipal h
  g := (exists_dim h).choose
  dim := (exists_dim h).choose_spec
  sym := by
    obtain ⟨-, w, hw, -⟩ := t.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  ample := h.ample
  ktriv := h.ktriv

theorem nonempty_genFib (P : Out.PolAV (Sp (𝓞 K))) : Nonempty (GenFib P) := by
  have := P.isAb.comm
  have h := isGrpPullback_pullback P.A (spMap (algebraMap (𝓞 K) K))
  obtain ⟨v, hv⟩ := TenDim.exists_isLieBasis _ (TorsionTauCompare.polOfPullback P _ h).smoothDim
  exact ⟨⟨TorsionTauCompare.polOfPullback P _ h, _, ⟨rfl, h, PolBaseChange.lbIso_refl (pull_isLB P.isLB _)⟩, v, hv⟩⟩

theorem dim_eq {ρ : 𝓞 K} {p q : ℕ} (T : PAT H (Sp (𝓞 K))) (hs : Splits E K) (ht : HasType H T.t.act ρ p q)
    (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) : T.g = Module.finrank ℚ E / 2 * (p + q) := by
  obtain ⟨F⟩ := nonempty_genFib T.pol
  exact (EigDec.eigen_decomposition E H K ρ T F p q hs ht hρ).2.2.2.1

theorem prod_ofFn_sum {M : Type} [CommMonoid M] {p q : ℕ} (f : Fin p ⊕ Fin q → M) :
    (List.ofFn fun i : Fin (p + q) => f (finSumFinEquiv.symm i)).prod = (∏ i, f (Sum.inl i)) * ∏ j, f (Sum.inr j) := by
  rw [List.prod_ofFn, Equiv.prod_comp finSumFinEquiv.symm f, Fintype.prod_sum_type]

theorem isog_iff {ρ : 𝓞 K} {p q : ℕ} (σ : K →+* ℂ) (hs : Splits E K) (hρ : ρ ^ 2 = -(H.d : 𝓞 K))
    (A : Bool → PAT H (Sp (𝓞 K))) (B : PAT H (Sp (𝓞 K))) (h₁ : HasType H (A true).t.act ρ 1 0)
    (h₂ : HasType H (A false).t.act ρ 0 1) (h₃ : HasType H B.t.act ρ p q)
    (φ : ∀ j : Fin p ⊕ Fin q, (A j.isLeft).t.G ⟶ B.t.G) (hφ : ∀ j, IsMonHom (φ j)) :
    EigenLatticeFibres.IsFinFlatSurj (EigenLatticeFibres.sumMap (A := (A true).t.G) (A' := (A false).t.G) (fun i => φ (Sum.inl i))
      fun j => φ (Sum.inr j)) ↔
    ∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ B.t.G,
      ∃ x : ∀ j : Fin p ⊕ Fin q, Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ (A j.isLeft).t.G,
        y = (List.ofFn fun i : Fin (p + q) => x (finSumFinEquiv.symm i) ≫ φ (finSumFinEquiv.symm i)).prod := by
  refine (isFinFlatSurj_sumMap_iff σ (A true).pol (A false).pol B.pol _ _ (fun i => hφ (Sum.inl i))
    (fun i => hφ (Sum.inr i)) ?_).trans (forall_congr' fun y => ⟨?_, ?_⟩)
  · change B.g = p * (A true).g + q * (A false).g
    rw [dim_eq _ hs h₁ hρ, dim_eq _ hs h₂ hρ, dim_eq _ hs h₃ hρ]
    ring
  · rintro ⟨x, x', h⟩
    exact ⟨fun j => Sum.rec (motive := fun j => _ ⟶ (A j.isLeft).t.G) x x' j,
      h.trans (prod_ofFn_sum fun j => Sum.rec (motive := fun j => _ ⟶ (A j.isLeft).t.G) x x' j ≫ φ j).symm⟩
  · rintro ⟨x, h⟩
    exact ⟨fun i => x (Sum.inl i), fun i => x (Sum.inr i), h.trans (prod_ofFn_sum fun j => x j ≫ φ j)⟩

variable {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ}

def toIndefiniteRowSideFullHecke (X : CMObj H K ρ σ₁ p q) : EigenLatticeFibres.CMObj H K ρ p q where
  A := (X.A true).t
  A' := (X.A false).t
  B := X.B.t
  prinA := isPrincipal _
  prinA' := isPrincipal _
  prinB := isPrincipal _
  sigA := (hasSig_iff _ _ _ _).2 ⟨X.ρ_sq, X.typeP⟩
  sigA' := (hasSig_iff _ _ _ _).2 ⟨X.ρ_sq, X.typeM⟩
  sigB := (hasSig_iff _ _ _ _).2 ⟨X.ρ_sq, X.typeB⟩
  ph i := X.φ (Sum.inl i)
  ph' j := X.φ (Sum.inr j)
  lin i := (isLinHom_iff _).2 (X.lin (Sum.inl i))
  lin' j := (isLinHom_iff _).2 (X.lin (Sum.inr j))
  isog := (isog_iff σ₁ X.split X.ρ_sq X.A X.B X.typeP X.typeM X.typeB X.φ fun j => (X.lin j).1).2 X.onto
  h i := X.hh (Sum.inl i)
  h' j := X.hh (Sum.inr j)
  pol i := (polId_iff σ₁ (X.A true) X.B _ (X.lin (Sum.inl i)).1 _).2 (X.weil (Sum.inl i))
  pol' j := (polId_iff σ₁ (X.A false) X.B _ (X.lin (Sum.inr j)).1 _).2 (X.weil (Sum.inr j))

def pure (Y : EigenLatticeFibres.CMObj H K ρ p q) : Bool → PAT H (Sp (𝓞 K))
  | true => patOf Y.A Y.prinA
  | false => patOf Y.A' Y.prinA'

def homs (Y : EigenLatticeFibres.CMObj H K ρ p q) : ∀ j : Fin p ⊕ Fin q, (pure Y j.isLeft).t.G ⟶ Y.B.G
  | Sum.inl i => Y.ph i
  | Sum.inr j => Y.ph' j

theorem homs_lin (Y : EigenLatticeFibres.CMObj H K ρ p q) : ∀ j, Serre.IsLinearHom (pure Y j.isLeft).t.act Y.B.act (homs Y j)
  | Sum.inl i => (isLinHom_iff _).1 (Y.lin i)
  | Sum.inr j => (isLinHom_iff _).1 (Y.lin' j)

def split_model_to_place_model (hs : EigenLatticeFibres.SplitsE E K) (σ₁ : K →+* ℂ) (Y : EigenLatticeFibres.CMObj H K ρ p q) : CMObj H K ρ σ₁ p q where
  split := (splits_iff E K).2 hs
  ρ_sq := Y.sigB.1
  A := pure Y
  B := patOf Y.B Y.prinB
  typeP := ((hasSig_iff _ _ _ _).1 Y.sigA).2
  typeM := ((hasSig_iff _ _ _ _).1 Y.sigA').2
  typeB := ((hasSig_iff _ _ _ _).1 Y.sigB).2
  hh := Sum.elim Y.h Y.h'
  φ := homs Y
  lin := homs_lin Y
  onto := (isog_iff σ₁ ((splits_iff E K).2 hs) Y.sigB.1 (pure Y) (patOf Y.B Y.prinB) ((hasSig_iff _ _ _ _).1 Y.sigA).2
    ((hasSig_iff _ _ _ _).1 Y.sigA').2 ((hasSig_iff _ _ _ _).1 Y.sigB).2 (homs Y) fun j => (homs_lin Y j).1).1 Y.isog
  weil
    | Sum.inl i => (polId_iff σ₁ (patOf Y.A Y.prinA) (patOf Y.B Y.prinB) _ (Y.lin i).1 _).1 (Y.pol i)
    | Sum.inr j => (polId_iff σ₁ (patOf Y.A' Y.prinA') (patOf Y.B Y.prinB) _ (Y.lin' j).1 _).1 (Y.pol' j)


theorem pat_ext {S : Scheme.{0}} {T T' : PAT H S} (h : T.t = T'.t) (hg : T.g = T'.g) : T = T' := by
  cases T
  cases T'
  cases h
  cases hg
  rfl

theorem toCMObj_injective : Function.Injective (toIndefiniteRowSideFullHecke : CMObj H K ρ σ₁ p q → _) := by
  intro X X' h
  have hA : X.A = X'.A := funext fun
    | true => pat_ext (congrArg EigenLatticeFibres.CMObj.A h)
      ((dim_eq _ X.split X.typeP X.ρ_sq).trans (dim_eq _ X.split X'.typeP X.ρ_sq).symm)
    | false => pat_ext (congrArg EigenLatticeFibres.CMObj.A' h)
      ((dim_eq _ X.split X.typeM X.ρ_sq).trans (dim_eq _ X.split X'.typeM X.ρ_sq).symm)
  have hB : X.B = X'.B := pat_ext (congrArg EigenLatticeFibres.CMObj.B h)
    ((dim_eq _ X.split X.typeB X.ρ_sq).trans (dim_eq _ X.split X'.typeB X.ρ_sq).symm)
  obtain ⟨_, _, A, B, _, _, _, hh, φ, _, _, _⟩ := X
  obtain ⟨_, _, A', B', _, _, _, hh', φ', _, _, _⟩ := X'
  cases hA
  cases hB
  unfold toIndefiniteRowSideFullHecke at h
  injection h with _ _ _ h₁ h₂ h₃ h₄
  obtain rfl : φ = φ' := funext fun
    | Sum.inl i => congrFun h₁ i
    | Sum.inr i => congrFun h₂ i
  obtain rfl : hh = hh' := funext fun
    | Sum.inl i => congrFun h₃ i
    | Sum.inr i => congrFun h₄ i
  rfl

def cmObjEquiv (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) :
    CMObj H K ρ σ₁ p q ≃ {_Y : EigenLatticeFibres.CMObj H K ρ p q // EigenLatticeFibres.SplitsE E K} where
  toFun X := ⟨toIndefiniteRowSideFullHecke X, (splits_iff E K).1 X.split⟩
  invFun Y := split_model_to_place_model Y.2 σ₁ Y.1
  left_inv _ := toCMObj_injective rfl
  right_inv _ := rfl

end Object

end GlobalTheory.CMSharedCompare
