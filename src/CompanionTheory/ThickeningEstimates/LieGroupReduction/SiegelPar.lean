import CompanionTheory.ThickeningEstimates.LieGroupReduction.SiegelCore
import CompanionTheory.ThickeningEstimates.SiegelDomainEstimates.LeHeightOfIsTorusElt
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarProductClosedCompactHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharEqOfIsOpenEmbeddingRestrict
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongrStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule

section
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open CompanionTheory.ThKEst (rId)
open CompanionTheory.ThKEst.Sieg (rId_add rId_zero' rId_snd rId_inf)

namespace CompanionTheory.ThKR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

variable (F E) in

def rIdU [IsTotallyReal F] (c : ℝ) : (AF F ⊗[F] E)ˣ where
  val := algebraMap (AF F) (AF F ⊗[F] E) (rId F c)
  inv := algebraMap (AF F) (AF F ⊗[F] E) (rId F (-c))
  val_inv := by rw [← map_mul, ← rId_add, add_neg_cancel, rId_zero', map_one]
  inv_val := by rw [← map_mul, ← rId_add, neg_add_cancel, rId_zero', map_one]

theorem val_rIdU [IsTotallyReal F] (c : ℝ) :
    (rIdU F E c : AF F ⊗[F] E) = algebraMap (AF F) (AF F ⊗[F] E) (rId F c) := rfl


theorem card_infinitePlace [IsTotallyReal F] : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
  have h2 := IsTotallyReal.nrComplexPlaces_eq_zero (K := F)
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

theorem norm_evInf_rId [IsTotallyReal F] (w : InfinitePlace F) (c : ℝ) : ‖evInf F w (rId F c)‖ = Real.exp c := by
  have e := rId_inf (F := F) w c
  have e2 : evInf F w (rId F c) = (rId F c).1 w := rfl
  rw [e2, ← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) ((rId F c).1 w), e]
  simp [Real.abs_exp]

theorem absE_rIdU [IsTotallyReal F] (h2 : Module.finrank F E = 2) (c : ℝ) :
    (GlobalTheory.Doubling.absE F E (rIdU F E c) : ℝ) = Real.exp (2 * Module.finrank ℚ F * c) := by
  haveI : Nontrivial (AF F) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact (evInf F w).toRingHom.domain_nontrivial
  have hn : Algebra.norm (AF F) (rIdU F E c : AF F ⊗[F] E) = rId F c ^ 2 := by
    rw [val_rIdU, Algebra.norm_algebraMap, Module.finrank_baseChange, h2]
  have hfin : ∀ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v (rIdU F E c)) = 1 := fun v => by
    rw [GlobalTheory.Doubling.absEv_unitFin, hn, map_pow]
    have e : evFin F v (rId F c) = 1 := by
      rw [evFin, AlgHom.comp_apply, show sndA F (rId F c) = 1 from rId_snd c, map_one]
    rw [e, one_pow, nnnorm_one]
  have hm : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w)]
  have hw : ∀ w : InfinitePlace F,
      (GlobalTheory.Doubling.absEw F E w (GlobalTheory.Doubling.unitInf F E w (rIdU F E c)) : ℝ) = Real.exp (2 * c) := fun w => by
    rw [GlobalTheory.Doubling.absEw_unitInf, hn, map_pow, hm, pow_one, coe_nnnorm, norm_pow, norm_evInf_rId, ← Real.exp_nat_mul]
    norm_num
  rw [GlobalTheory.Doubling.absE_apply, finprod_eq_one_of_forall_eq_one hfin, mul_one, NNReal.coe_prod,
    Finset.prod_congr rfl fun w _ => hw w, Finset.prod_const, Finset.card_univ, card_infinitePlace,
    ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

variable (σ) in
theorem sigRA_sigRA (h : IsCMExt F E σ) (x : AF F ⊗[F] E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, sigma_sigma h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigRA_inclR (e : E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [sigR, inclR]

theorem cT_map_inclR {a b : Type} (P : Matrix a b E) :
    (Formalism.UG.cT (σ : E →+* E) P).map (inclR (F := F) (AF F)) = Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (P.map (inclR (F := F) (AF F))) :=
  Matrix.ext fun i j => by simp [cT, sigRA_inclR]

structure PFr {R : Type} [CommRing R] (s : R →+* R) (Jm : Matrix (Fin n) (Fin n) R) (Xm Ym : Matrix (Fin n) (Fin r) R) :
    Prop where
  ss : ∀ x, s (s x) = x
  herm : cT s Jm = Jm
  xx : cT s Xm * Jm * Xm = 0
  yy : cT s Ym * Jm * Ym = 0
  xy : cT s Xm * Jm * Ym = 1

section PFr

variable {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R} {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem PFr.cc (hF : PFr s Jm Xm Ym) {a b : Type} (P : Matrix a b R) : cT s (cT s P) = P :=
  Matrix.ext fun _ _ => hF.ss _

theorem PFr.yx (hF : PFr s Jm Xm Ym) : cT s Ym * Jm * Xm = 1 := by
  have := congrArg (cT s) hF.xy
  rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hF.cc, hF.herm, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this

theorem pgram_unitary {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * Jm * g = Jm) {a b : Type}
    (P : Matrix (Fin n) a R) (Q : Matrix (Fin n) b R) : cT s (g * P) * Jm * (g * Q) = cT s P * Jm * Q := by
  conv_rhs => rw [← hg]
  simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]

theorem PFr.inv_coef (hF : PFr s Jm Xm Ym) {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * Jm * g = Jm)
    {B : Matrix (Fin r) (Fin r) R} (hB : g * Xm = Xm * B) : cT s (cT s Xm * Jm * (g * Ym)) * B = 1 := by
  have h2 : cT s B * (cT s Xm * Jm * (g * Ym)) = 1 := by
    rw [← hF.xy, ← pgram_unitary hg Xm Ym, hB, Formalism.UG.cT_mul]
    simp only [Matrix.mul_assoc]
  have := congrArg (cT s) h2
  rwa [Formalism.UG.cT_mul, hF.cc, Formalism.UG.cT_one] at this

def coefM (s : R →+* R) (Jm : Matrix (Fin n) (Fin n) R) (Xm Ym : Matrix (Fin n) (Fin r) R) (g : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin r) (Fin r) R :=
  cT s Ym * Jm * (g * Xm)

end PFr

theorem pfrA (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    PFr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (GlobalTheory.SiegelSet.adMat F X) (GlobalTheory.SiegelSet.adMat F Y) := by
  refine ⟨sigRA_sigRA σ h, ?_, ?_, ?_, ?_⟩
  · have e : Formalism.UG.cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
    unfold JR
    rw [← cT_map_inclR, e]
  · unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hW.xx, Matrix.map_zero _ (map_zero _)]
  · unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hW.yy, Matrix.map_zero _ (map_zero _)]
  · unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul, ← Matrix.map_mul, hW.xy, Matrix.map_one _ (map_zero _) (map_one _)]

theorem unitaryA_matHom (p : GAd σ J) :
    Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (matHom _ σ J p).1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J * (matHom _ σ J p).1 = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J :=
  (show ↥(HR (AF F) σ J) from p).2

variable (σ J X Y) in

def Bm (p : GAd σ J) : Matrix (Fin r) (Fin r) (AF F ⊗[F] E) :=
  coefM (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (GlobalTheory.SiegelSet.adMat F X) (GlobalTheory.SiegelSet.adMat F Y)
    (matHom _ σ J p).1

section Bm

variable (hF : PFr (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J) (GlobalTheory.SiegelSet.adMat F X) (GlobalTheory.SiegelSet.adMat F Y))
include hF

theorem Bm_eq {p : GAd σ J} {B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (e : (matHom _ σ J p).1 * GlobalTheory.SiegelSet.adMat F X = GlobalTheory.SiegelSet.adMat F X * B) : Bm σ J X Y p = B := by
  rw [Bm, coefM, e, ← Matrix.mul_assoc, hF.yx, Matrix.one_mul]

theorem mem_minPar_iff {p : GAd σ J} : p ∈ minPar σ J X ↔
    (Bm σ J X Y p).BlockTriangular id ∧ (matHom _ σ J p).1 * GlobalTheory.SiegelSet.adMat F X = GlobalTheory.SiegelSet.adMat F X * Bm σ J X Y p := by
  constructor
  · rintro ⟨B, hB, e⟩
    rw [Bm_eq hF e]
    exact ⟨hB, e⟩
  · rintro ⟨hB, e⟩
    exact ⟨_, hB, e⟩

theorem Bm_mul {p q : GAd σ J} (hp : p ∈ minPar σ J X) (hq : q ∈ minPar σ J X) :
    Bm σ J X Y (p * q) = Bm σ J X Y p * Bm σ J X Y q := by
  have ep := ((mem_minPar_iff hF).1 hp).2
  have eq := ((mem_minPar_iff hF).1 hq).2
  apply Bm_eq hF
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, eq, ← Matrix.mul_assoc, ep, Matrix.mul_assoc]

theorem Bm_one : Bm σ J X Y (1 : GAd σ J) = 1 :=
  Bm_eq hF (by rw [map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])

end Bm

theorem diag_mul_bt {R : Type} [CommRing R] {B C : Matrix (Fin r) (Fin r) R} (hB : B.BlockTriangular id)
    (hC : C.BlockTriangular id) (i : Fin r) : (B * C) i i = B i i * C i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hl | hl
    · rw [hB hl, zero_mul]
    · rw [hC hl, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem mul_mem_minimal_parabolic {p q : GAd σ J} (hp : p ∈ minPar σ J X) (hq : q ∈ minPar σ J X) :
    p * q ∈ minPar σ J X := by
  obtain ⟨B, hB, e⟩ := hp
  obtain ⟨C, hC, e'⟩ := hq
  refine ⟨B * C, hB.mul hC, ?_⟩
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', ← Matrix.mul_assoc, e, Matrix.mul_assoc]

theorem inv_mem_minimal_parabolic (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) : p⁻¹ ∈ minPar σ J X := by
  obtain ⟨B, hB, e⟩ := hp
  obtain ⟨Q, h3⟩ : ∃ Q, Q * B = 1 := ⟨_, (pfrA h hJ hW).inv_coef (unitaryA_matHom p) e⟩
  have h4 : B * Q = 1 := mul_eq_one_comm.1 h3
  haveI : Invertible B := ⟨Q, h3, h4⟩
  have hinv : B⁻¹ = Q := Matrix.inv_eq_left_inv h3
  refine ⟨Q, by rw [← hinv]; exact Matrix.blockTriangular_inv_of_blockTriangular hB, ?_⟩
  have e2 : (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  calc (matHom _ σ J p⁻¹).1 * GlobalTheory.SiegelSet.adMat F X = (matHom _ σ J p⁻¹).1 * (GlobalTheory.SiegelSet.adMat F X * (B * Q)) := by
        rw [h4, Matrix.mul_one]
    _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * GlobalTheory.SiegelSet.adMat F X * Q := by
        rw [← Matrix.mul_assoc (GlobalTheory.SiegelSet.adMat F X), ← e]
        simp only [Matrix.mul_assoc]
    _ = GlobalTheory.SiegelSet.adMat F X * Q := by rw [e2, Matrix.one_mul]

theorem continuous_matHom_val : Continuous fun p : GAd σ J => (matHom _ σ J p).1 :=
  Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous

variable (σ J X Y) in

def uU (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J} (hp : p ∈ minPar σ J X)
    (hp' : p⁻¹ ∈ minPar σ J X) (i : Fin r) : (AF F ⊗[F] E)ˣ where
  val := Bm σ J X Y p i i
  inv := Bm σ J X Y p⁻¹ i i
  val_inv := by
    have hF := pfrA h hJ hW
    rw [← diag_mul_bt ((mem_minPar_iff hF).1 hp).1 ((mem_minPar_iff hF).1 hp').1, ← Bm_mul hF hp hp',
      mul_inv_cancel, Bm_one hF, Matrix.one_apply_eq]
  inv_val := by
    have hF := pfrA h hJ hW
    rw [← diag_mul_bt ((mem_minPar_iff hF).1 hp').1 ((mem_minPar_iff hF).1 hp).1, ← Bm_mul hF hp' hp,
      inv_mul_cancel, Bm_one hF, Matrix.one_apply_eq]

theorem val_uU (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) (hp' : p⁻¹ ∈ minPar σ J X) (i : Fin r) :
    (uU σ J X Y h hJ hW hp hp' i : AF F ⊗[F] E) = Bm σ J X Y p i i := rfl

variable (σ J X Y) in

def uP (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (P : Subgroup (GAd σ J))
    (hP : ∀ p, p ∈ P ↔ p ∈ minPar σ J X) (p : P) (i : Fin r) : (AF F ⊗[F] E)ˣ :=
  uU σ J X Y h hJ hW ((hP _).1 p.2) ((hP _).1 (P.inv_mem p.2)) i

end CompanionTheory.ThKR

end
end

section
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology Set
open scoped NNReal ENNReal Pointwise

namespace CompanionTheory.ThKR.Sieg

section Retract

variable {H N : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
  [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
  [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N]

theorem char_eq_of_retract (ι : N →* H) (hι : Continuous ι) (π : H → N) (hπ : Continuous π)
    (hmul : ∀ x p, π (ι x * p) = x * π p) (φ : H ≃ₜ* H) (ψ : N ≃ₜ* N) (h1 : ∀ p, π (φ p) = ψ (π p))
    (h2 : ∀ p, (ι (π (φ p)))⁻¹ * φ p = (ι (π p))⁻¹ * p) : mulEquivHaarChar φ = mulEquivHaarChar ψ := by
  let l : H → H := fun p => (ι (π p))⁻¹ * p
  have hl : Continuous l := (hι.comp hπ).inv.mul continuous_id
  obtain ⟨E, hE, hE1⟩ := exists_compact_mem_nhds (l 1)
  let T : Set H := l ⁻¹' E
  let ν : Measure H := haar
  let m : Measure N := (ν.restrict T).map π
  have hm : ∀ A, MeasurableSet A → m A = ν (π ⁻¹' A ∩ T) := fun A hA => by
    rw [Measure.map_apply hπ.measurable hA, Measure.restrict_apply (hπ.measurable hA)]
  have : IsMulLeftInvariant m := (forall_measure_preimage_mul_iff m).1 fun x A hA => by
    rw [hm _ hA, hm _ (measurable_const_mul x hA), ← measure_preimage_mul ν (ι x) (π ⁻¹' A ∩ T)]
    congr 1
    ext p
    simp [T, l, hmul, mul_assoc]
  have : IsFiniteMeasureOnCompacts m := ⟨fun C hC => by
    rw [hm _ hC.measurableSet]
    refine (measure_mono ?_).trans_lt ((hC.image hι).mul hE).measure_lt_top
    rintro p ⟨hp, hp'⟩
    exact ⟨_, ⟨_, hp, rfl⟩, _, hp', by simp [l]⟩⟩
  have hc := isMulLeftInvariant_eq_smul m (haar : Measure N)
  set c := haarScalarFactor m (haar : Measure N)
  have hc0 : c ≠ 0 := fun e => by
    have h0 : m univ = 0 := by rw [hc, e]; simp
    rw [hm _ MeasurableSet.univ, preimage_univ, univ_inter] at h0
    exact (measure_pos_of_mem_nhds ν (hl.continuousAt.preimage_mem_nhds hE1)).ne' h0
  obtain ⟨A, hA, hA1⟩ := exists_compact_mem_nhds (1 : N)
  have hA' : IsCompact (ψ ⁻¹' A) := ψ.toHomeomorph.isCompact_preimage.2 hA
  have e1 := mulEquivHaarChar_smul_preimage ν (X := π ⁻¹' A ∩ T) φ
  have e2 := mulEquivHaarChar_smul_preimage (haar : Measure N) (X := A) ψ
  have e3 : φ ⁻¹' (π ⁻¹' A ∩ T) = π ⁻¹' (ψ ⁻¹' A) ∩ T := by
    ext p
    simp only [mem_preimage, mem_inter_iff, T, l]
    rw [h2 p, h1 p]
  rw [e3, ← hm _ hA'.measurableSet, ← hm _ hA.measurableSet, hc, Measure.smul_apply, Measure.smul_apply, ← e2,
    smul_comm c] at e1
  have h3 : (c • (haar : Measure N) (ψ ⁻¹' A)) ≠ 0 := by
    rw [ENNReal.smul_def, smul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast hc0) (measure_pos_of_mem_nhds _
      (ψ.continuous.continuousAt.preimage_mem_nhds (x := 1) (by simpa using hA1))).ne'
  have h4 : (c • (haar : Measure N) (ψ ⁻¹' A)) ≠ ⊤ := by
    rw [ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hA'.measure_lt_top.ne
  rw [ENNReal.smul_def, ENNReal.smul_def (mulEquivHaarChar ψ), smul_eq_mul, smul_eq_mul] at e1
  exact_mod_cast (ENNReal.mul_left_inj h3 h4).1 e1

end Retract

section Heis

variable {A B : Type} [AddCommGroup A] [AddCommGroup B]

@[nolint unusedArguments]
def Heis (_ : A →+ A →+ B) : Type := A × B

variable (β : A →+ A →+ B)

instance : Group (Heis β) where
  mul x y := (x.1 + y.1, x.2 + y.2 + β x.1 y.1)
  one := (0, 0)
  inv x := (-x.1, -x.2 + β x.1 x.1)
  mul_assoc x y z := Prod.ext (add_assoc _ _ _) (by
    change x.2 + y.2 + β x.1 y.1 + z.2 + β (x.1 + y.1) z.1 = x.2 + (y.2 + z.2 + β y.1 z.1) + β x.1 (y.1 + z.1)
    simp only [map_add, AddMonoidHom.add_apply]
    abel)
  one_mul x := Prod.ext (zero_add _) (by change 0 + x.2 + β 0 x.1 = x.2; simp)
  mul_one x := Prod.ext (add_zero _) (by change x.2 + 0 + β x.1 0 = x.2; simp)
  inv_mul_cancel x := Prod.ext (neg_add_cancel _) (by
    change -x.2 + β x.1 x.1 + x.2 + β (-x.1) x.1 = 0; simp)

variable [TopologicalSpace A] [TopologicalSpace B]

instance : TopologicalSpace (Heis β) := inferInstanceAs (TopologicalSpace (A × B))

instance [T2Space A] [T2Space B] : T2Space (Heis β) := inferInstanceAs (T2Space (A × B))

instance [LocallyCompactSpace A] [LocallyCompactSpace B] : LocallyCompactSpace (Heis β) :=
  inferInstanceAs (LocallyCompactSpace (A × B))

instance [SecondCountableTopology A] [SecondCountableTopology B] : SecondCountableTopology (Heis β) :=
  inferInstanceAs (SecondCountableTopology (A × B))

instance [MeasurableSpace A] [MeasurableSpace B] : MeasurableSpace (Heis β) :=
  inferInstanceAs (MeasurableSpace (A × B))

instance [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] [SecondCountableTopology A] :
    BorelSpace (Heis β) := inferInstanceAs (BorelSpace (A × B))

variable [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]

theorem Heis.isTopologicalGroup (hβ : Continuous fun p : A × A => β p.1 p.2) : IsTopologicalGroup (Heis β) where
  continuous_mul := by
    change Continuous fun p : (A × B) × A × B => ((p.1.1 + p.2.1, p.1.2 + p.2.2 + β p.1.1 p.2.1) : A × B)
    exact (continuous_fst.fst.add continuous_snd.fst).prodMk ((continuous_fst.snd.add continuous_snd.snd).add
      (hβ.comp (continuous_fst.fst.prodMk continuous_snd.fst)))
  continuous_inv := by
    change Continuous fun p : A × B => ((-p.1, -p.2 + β p.1 p.1) : A × B)
    exact continuous_fst.neg.prodMk (continuous_snd.neg.add (hβ.comp (continuous_fst.prodMk continuous_fst)))

variable [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
  [LocallyCompactSpace B] [SecondCountableTopology B] [T2Space B] [MeasurableSpace B] [BorelSpace B]

theorem Heis.char_eq [IsTopologicalGroup (Heis β)] (hβ : Continuous fun p : A × A => β p.1 p.2) (ψ : Heis β ≃ₜ* Heis β)
    (θ₁ : A ≃ₜ+ A) (θ₂ : B ≃ₜ+ B) (h : ∀ x, ψ x = (θ₁ x.1, θ₂ x.2)) :
    mulEquivHaarChar ψ = addEquivAddHaarChar θ₁ * addEquivAddHaarChar θ₂ := by
  let μ₁ : Measure A := addHaar
  let μ₂ : Measure B := addHaar
  let μ : Measure (Heis β) := μ₁.prod μ₂
  have : IsFiniteMeasureOnCompacts μ := inferInstanceAs (IsFiniteMeasureOnCompacts (μ₁.prod μ₂))
  have : IsOpenPosMeasure μ := inferInstanceAs (IsOpenPosMeasure (μ₁.prod μ₂))
  have : IsMulLeftInvariant μ := ⟨fun x => by
    refine (MeasurePreserving.skew_product (μa := μ₁) (μc := μ₂) (μd := μ₂) (measurePreserving_add_left μ₁ x.1)
      (g := fun a b => x.2 + b + β x.1 a) ?_ (.of_forall fun a => ?_)).map_eq
    · exact ((continuous_const.add continuous_snd).add (hβ.comp (continuous_const.prodMk continuous_fst))).measurable
    · rw [show (fun b => x.2 + b + β x.1 a) = fun b => (x.2 + β x.1 a) + b from funext fun b => by abel]
      exact map_add_left_eq_self μ₂ _⟩
  have : IsHaarMeasure μ := {}
  obtain ⟨U, hU, hU0⟩ := exists_compact_mem_nhds (0 : A)
  obtain ⟨V, hV, hV0⟩ := exists_compact_mem_nhds (0 : B)
  have e := mulEquivHaarChar_smul_preimage μ (X := (U ×ˢ V : Set (A × B))) ψ
  have e1 := addEquivAddHaarChar_smul_preimage μ₁ (X := U) θ₁
  have e2 := addEquivAddHaarChar_smul_preimage μ₂ (X := V) θ₂
  have e3 : ψ ⁻¹' (U ×ˢ V : Set (A × B)) = ((θ₁ ⁻¹' U) ×ˢ (θ₂ ⁻¹' V) : Set (A × B)) := by
    ext x
    change ψ x ∈ (U ×ˢ V : Set (A × B)) ↔ _
    rw [h]
    rfl
  rw [e3] at e
  change _ • (μ₁.prod μ₂) _ = (μ₁.prod μ₂) _ at e
  rw [prod_prod, prod_prod, ← e1, ← e2] at e
  simp only [ENNReal.smul_def, smul_eq_mul] at e
  rw [mul_mul_mul_comm, ← ENNReal.coe_mul] at e
  refine ENNReal.coe_injective ((ENNReal.mul_left_inj (mul_ne_zero ?_ ?_) (ENNReal.mul_ne_top ?_ ?_)).1 e)
  · exact (measure_pos_of_mem_nhds _ (θ₁.continuous.continuousAt.preimage_mem_nhds (x := 0) (by simpa using hU0))).ne'
  · exact (measure_pos_of_mem_nhds _ (θ₂.continuous.continuousAt.preimage_mem_nhds (x := 0) (by simpa using hV0))).ne'
  · exact (θ₁.toHomeomorph.isCompact_preimage.2 hU).measure_lt_top.ne
  · exact (θ₂.toHomeomorph.isCompact_preimage.2 hV).measure_lt_top.ne

end Heis

section Bound

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {r : ℕ}

theorem isClosed_image_section {X : Type} [TopologicalSpace X] [T2Space X] (τ : X → Fin r → ℝ) (hτ : Continuous τ)
    (a : (Fin r → ℝ) → X) (ha : Continuous a) (h : ∀ t, τ (a t) = t) {D : Set (Fin r → ℝ)} (hD : IsClosed D) :
    IsClosed (a '' D) :=
  (Function.LeftInverse.isClosedEmbedding h hτ ha).isClosedMap _ hD

theorem lintegral_tau (ν : Measure G) [ν.IsHaarMeasure] (τ : G → Fin r → ℝ) (hτ : Continuous τ)
    (hτm : ∀ p q, τ (p * q) = τ p + τ q) (a : (Fin r → ℝ) → G) (ha : Continuous a) (hadd : ∀ s t, a (s + t) = a s * a t)
    (hτa : ∀ t, τ (a t) = t) (ρ : (Fin r → ℝ) → ℝ) (hρ : Continuous ρ) (hρa : ∀ s t, ρ (s + t) = ρ s + ρ t)
    (hmod : ∀ s, ν.map (· * a s) = ENNReal.ofReal (Real.exp (ρ s)) • ν) {Ω : Set G} (hΩ : IsCompact Ω)
    (hΩτ : ∀ p ∈ Ω, τ p = 0) :
    ∃ C : ℝ≥0, ∀ h : (Fin r → ℝ) → ℝ≥0∞, Measurable h →
      ∫⁻ p in Ω * range a, h (τ p) ∂ν = C * ∫⁻ t, h t * ENNReal.ofReal (Real.exp (-ρ t)) := by
  have hT : IsClosed (Ω * range a) := by
    rw [← image_univ]
    exact (isClosed_image_section τ hτ a ha hτa isClosed_univ).mul_left_of_isCompact hΩ
  set T := Ω * range a with hTdef
  let w : G → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (ρ (τ p)))
  have hw : Measurable w := (Real.continuous_exp.comp (hρ.comp hτ)).measurable.ennreal_ofReal
  let m : Measure (Fin r → ℝ) := ((ν.restrict T).withDensity w).map τ
  have hm : ∀ g : (Fin r → ℝ) → ℝ≥0∞, Measurable g → ∫⁻ t, g t ∂m = ∫⁻ p, T.indicator (fun p => w p * g (τ p)) p ∂ν :=
    fun g hg => by
      rw [lintegral_map hg hτ.measurable, lintegral_withDensity_eq_lintegral_mul _ hw (g := fun p => g (τ p)) (hg.comp hτ.measurable),
        lintegral_indicator hT.measurableSet]
      rfl
  have hTa : ∀ s p, p * a s ∈ T ↔ p ∈ T := by
    have : ∀ s p, p ∈ T → p * a s ∈ T := by
      rintro s _ ⟨p, hp, _, ⟨t, rfl⟩, rfl⟩
      exact ⟨p, hp, _, ⟨t + s, rfl⟩, by simp [hadd, mul_assoc]⟩
    have h0 : a 0 = 1 := by simpa using hadd 0 0
    refine fun s p => ⟨fun h => ?_, this s p⟩
    have := this (-s) _ h
    rwa [mul_assoc, ← hadd, add_neg_cancel, h0, mul_one] at this
  have : IsAddLeftInvariant m := ⟨fun s => by
    refine Measure.ext_of_lintegral _ fun g hg => ?_
    rw [lintegral_map hg (measurable_const_add s), hm (fun t => g (s + t)) (hg.comp (measurable_const_add s)), hm _ hg]
    have hG : Measurable (T.indicator fun p => w p * g (τ p)) :=
      (hw.mul (hg.comp hτ.measurable)).indicator hT.measurableSet
    have e := lintegral_map (μ := ν) hG (measurable_mul_const (a s))
    rw [hmod, lintegral_smul_measure, smul_eq_mul] at e
    have h0 : ENNReal.ofReal (Real.exp (ρ s)) ≠ 0 := by simp [Real.exp_pos]
    rw [← ENNReal.mul_right_inj h0 ENNReal.ofReal_ne_top, e, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ T
    · rw [indicator_of_mem hp, indicator_of_mem ((hTa s p).2 hp)]
      simp only [w, hτm, hτa, hρa, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, add_comm s]
      ring
    · rw [indicator_of_notMem hp, indicator_of_notMem (mt (hTa s p).1 hp), mul_zero]⟩
  have : IsFiniteMeasureOnCompacts m := ⟨fun C hC => by
    obtain ⟨B, hB⟩ := hC.bddAbove_image hρ.continuousOn
    rw [← lintegral_indicator_one hC.measurableSet, hm _ (measurable_one.indicator hC.measurableSet)]
    have hK : IsCompact (Ω * a '' C) := hΩ.mul (hC.image ha)
    refine lt_of_le_of_lt (lintegral_mono (g := (Ω * a '' C).indicator fun _ => ENNReal.ofReal (Real.exp B)) fun p => ?_) ?_
    · by_cases hp : p ∈ T
      · by_cases hp' : τ p ∈ C
        · obtain ⟨q, hq, _, ⟨t, rfl⟩, rfl⟩ := hp
          have e : τ (q * a t) = t := by rw [hτm, hτa, hΩτ q hq, zero_add]
          simp only [e] at hp'
          rw [indicator_of_mem (show q * a t ∈ T from ⟨q, hq, _, ⟨t, rfl⟩, rfl⟩),
            indicator_of_mem (show q * a t ∈ Ω * a '' C from ⟨q, hq, _, ⟨t, hp', rfl⟩, rfl⟩), e, indicator_of_mem hp']
          simp only [w, e, Pi.one_apply, mul_one]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hB ⟨t, hp', rfl⟩))
        · rw [indicator_of_mem hp, indicator_of_notMem hp', mul_zero]
          exact zero_le
      · rw [indicator_of_notMem hp]
        exact zero_le
    · rw [lintegral_indicator_const hK.measurableSet]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top⟩
  refine ⟨addHaarScalarFactor m volume, fun h hh => ?_⟩
  have hg : Measurable fun t => h t * ENNReal.ofReal (Real.exp (-ρ t)) :=
    hh.mul (Real.continuous_exp.comp hρ.neg).measurable.ennreal_ofReal
  have e := hm _ hg
  rw [isAddLeftInvariant_eq_smul m volume, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul,
    lintegral_indicator hT.measurableSet] at e
  rw [e]
  refine lintegral_congr fun p => ?_
  rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel]
  simp

theorem lintegral_siegel_le (μ : Measure G) [μ.IsHaarMeasure] (P K : Subgroup G) (hP : IsClosed (P : Set G))
    (hK : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) [LocallyCompactSpace P]
    (τ : P → Fin r → ℝ) (hτ : Continuous τ)
    (hτm : ∀ p q, τ (p * q) = τ p + τ q) (a : (Fin r → ℝ) → P) (ha : Continuous a) (hadd : ∀ s t, a (s + t) = a s * a t)
    (hτa : ∀ t, τ (a t) = t) (ρ : (Fin r → ℝ) → ℝ) (hρ : Continuous ρ) (hρa : ∀ s t, ρ (s + t) = ρ s + ρ t)
    (hmod : ∀ s, (haar : Measure P).map (· * a s) = ENNReal.ofReal (Real.exp (ρ s)) • haar) {Ω : Set G}
    (hΩ : IsCompact Ω) (hΩτ : ∀ p ∈ Ω, ∃ h : p ∈ P, τ ⟨p, h⟩ = 0) (hc : ∀ m : P, m.1 ∈ K → ∀ t, a t * m = m * a t) :
    ∃ C : ℝ≥0, ∀ (D : Set (Fin r → ℝ)) (S : Set G), MeasurableSet D → MeasurableSet S →
      (∀ g ∈ S, ∃ p ∈ Ω, ∃ t ∈ D, ∃ k ∈ K, g = p * a t * k) →
      ∀ (f : G → ℝ≥0∞) (h : (Fin r → ℝ) → ℝ≥0∞), Measurable h →
        (∀ p ∈ Ω, ∀ t ∈ D, ∀ k ∈ K, f (p * a t * k) ≤ h t) →
        ∫⁻ g in S, f g ∂μ ≤ C * ∫⁻ t in D, h t * ENNReal.ofReal (Real.exp (-ρ t)) := by
  have hι : IsClosedEmbedding ((↑) : P → G) := hP.isClosedEmbedding_subtypeVal
  have : SecondCountableTopology P := hι.isEmbedding.secondCountableTopology
  have hL : IsCompact (((↑) : P → G) ⁻¹' K) := hι.isCompact_preimage hK
  have hτL : ∀ m : P, m.1 ∈ K → τ m = 0 := fun m hm => by
    obtain ⟨B, hB⟩ := (hL.image hτ).isBounded.exists_norm_le
    have h1 : τ 1 = 0 := by simpa using hτm 1 1
    have h2 : ∀ j : ℕ, τ (m ^ j) = (j : ℝ) • τ m := fun j => by
      induction j with
      | zero => simpa using h1
      | succ j ih => rw [pow_succ, hτm, ih]; simp [add_smul]
    by_contra h0
    obtain ⟨j, hj⟩ := exists_nat_gt (B / ‖τ m‖)
    have h3 := hB _ ⟨m ^ j, K.pow_mem hm j, rfl⟩
    rw [h2, norm_smul, Real.norm_natCast] at h3
    rw [div_lt_iff₀ (norm_pos_iff.2 h0)] at hj
    linarith
  have hΩ' : IsCompact (((↑) : P → G) ⁻¹' Ω * ((↑) : P → G) ⁻¹' K) := (hι.isCompact_preimage hΩ).mul hL
  obtain ⟨C, hC⟩ := lintegral_tau (haar : Measure P) τ hτ hτm a ha hadd hτa ρ hρ hρa hmod hΩ' (by
    rintro _ ⟨p, hp, m, hm, rfl⟩
    obtain ⟨_, e⟩ := hΩτ _ hp
    rw [hτm, hτL m hm, e, add_zero])
  have hT : IsClosed (((↑) : P → G) ⁻¹' Ω * ((↑) : P → G) ⁻¹' K * range a) := by
    rw [← image_univ]
    exact (isClosed_image_section τ hτ a ha hτa isClosed_univ).mul_left_of_isCompact hΩ'
  set T := ((↑) : P → G) ⁻¹' Ω * ((↑) : P → G) ⁻¹' K * range a with hTdef
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let κ : Measure K := haarMeasure ⊤
  have hκ : κ univ = 1 := by simpa [κ] using haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
  have hmP : Measurable ((↑) : P → G) := measurable_subtype_coe
  have hmK : Measurable ((↑) : K → G) := measurable_subtype_coe
  obtain ⟨c, -, hc', hΦ⟩ := GlobalTheory.CompanionTheory.HaarPK.haarProductClosedCompact_holds G μ inferInstance inferInstance
    (NeZero.ne μ) P K hP hK hPK ((haar : Measure P).map (↑)) (κ.map (↑))
    (by rw [Measure.map_apply hmP hP.measurableSet.compl]; simp [preimage])
    (fun p hp => by
      rw [Measure.map_map (measurable_const_mul p) hmP]
      conv_rhs => rw [← map_mul_left_eq_self (haar : Measure P) ⟨p, hp⟩, Measure.map_map hmP (measurable_const_mul _)]
      rfl)
    (fun s hs => by rw [Measure.map_apply hmP hs.measurableSet]; exact (hι.isCompact_preimage hs).measure_lt_top.ne)
    (by rw [Ne, Measure.map_eq_zero_iff hmP.aemeasurable]; exact NeZero.ne _)
    (by rw [Measure.map_apply hmK MeasurableSet.univ, preimage_univ, hκ])
    (by rw [Measure.map_apply hmK hK.measurableSet.compl]; simp [preimage])
    (fun p hp => by
      rw [Measure.map_map (measurable_const_mul p) hmK]
      conv_rhs => rw [← map_mul_left_eq_self κ ⟨p, hp⟩, Measure.map_map hmK (measurable_const_mul _)]
      rfl)
  refine ⟨c.toNNReal * C, fun D S hD hS hSΩ f h hh hf => ?_⟩
  rw [← lintegral_indicator hS, lintegral_eq_nnreal]
  refine iSup₂_le fun φ hφ => ?_
  have hφm : Measurable fun g => (φ g : ℝ≥0∞) := φ.measurable.coe_nnreal_ennreal
  rw [← SimpleFunc.lintegral_eq_lintegral]
  change ∫⁻ g, (φ g : ℝ≥0∞) ∂μ ≤ _
  rw [hΦ _ hφm, ENNReal.coe_mul, ENNReal.coe_toNNReal hc', mul_assoc, ← lintegral_indicator hD]
  have e : D.indicator (fun t => h t * ENNReal.ofReal (Real.exp (-ρ t))) =
      fun t => D.indicator h t * ENNReal.ofReal (Real.exp (-ρ t)) := funext fun t => by
    by_cases ht : t ∈ D <;> simp [ht]
  rw [e, ← hC _ (hh.indicator hD), ← lintegral_indicator hT.measurableSet]
  refine mul_le_mul_right ?_ _
  refine (lintegral_map_le _ ((↑) : P → G)).trans (lintegral_mono fun p => ?_)
  refine (lintegral_map_le _ ((↑) : K → G)).trans ?_
  refine (lintegral_mono (g := fun _ => T.indicator (fun p => D.indicator h (τ p)) p) fun k => ?_).trans
    (by rw [lintegral_const, hκ, mul_one])
  refine (hφ _).trans ?_
  by_cases hg : p.1 * k.1 ∈ S
  · obtain ⟨q, hq, t, ht, k', hk', e⟩ := hSΩ _ hg
    obtain ⟨hqP, hq0⟩ := hΩτ q hq
    let m : P := (⟨q, hqP⟩ * a t)⁻¹ * p
    have hm : m.1 = k' * k.1⁻¹ := by
      change (q * a t)⁻¹ * p.1 = _
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e, mul_inv_cancel_right]
    have hmK : m.1 ∈ K := hm ▸ K.mul_mem hk' (K.inv_mem k.2)
    have hp : p = ⟨q, hqP⟩ * m * a t := by rw [mul_assoc, ← hc m hmK, ← mul_assoc, mul_inv_cancel_left]
    have hpT : p ∈ T := ⟨_, ⟨⟨q, hqP⟩, hq, m, hmK, rfl⟩, _, ⟨t, rfl⟩, hp.symm⟩
    have hτp : τ p = t := by rw [hp, hτm, hτm, hq0, hτL m hmK, hτa]; simp
    rw [indicator_of_mem hg, indicator_of_mem hpT, hτp, indicator_of_mem ht, e]
    exact hf q hq t ht k' hk'
  · rw [indicator_of_notMem hg]
    exact zero_le

end Bound

end CompanionTheory.ThKR.Sieg

end
end

section
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology Set Matrix
open Formalism.UG (cT cT_mul cT_one)
open scoped NNReal ENNReal Pointwise

namespace CompanionTheory.ThKR.Sieg

variable {R : Type} [CommRing R] {s : R →+* R} {n k : ℕ} {J : Matrix (Fin n) (Fin n) R} {X Y : Matrix (Fin n) (Fin k) R}

section Alg

theorem cT_add {a b : Type} (P Q : Matrix a b R) : cT s (P + Q) = cT s P + cT s Q := Matrix.ext fun _ _ => map_add s _ _

theorem cT_sub {a b : Type} (P Q : Matrix a b R) : cT s (P - Q) = cT s P - cT s Q := Matrix.ext fun _ _ => map_sub s _ _

theorem cT_neg {a b : Type} (P : Matrix a b R) : cT s (-P) = -cT s P := Matrix.ext fun _ _ => map_neg s _

theorem cT_zero {a b : Type} : cT s (0 : Matrix a b R) = 0 := Matrix.ext fun _ _ => map_zero s

theorem cT_smul {a b : Type} (c : R) (P : Matrix a b R) : cT s (c • P) = s c • cT s P :=
  Matrix.ext fun _ _ => map_mul s _ _

variable (s J X Y) in

structure Fr : Prop where
  ss : ∀ x, s (s x) = x
  herm : cT s J = J
  xx : cT s X * J * X = 0
  yy : cT s Y * J * Y = 0
  xy : cT s X * J * Y = 1

theorem Fr.cc (h : Fr s J X Y) {a b : Type} (P : Matrix a b R) : cT s (cT s P) = P := Matrix.ext fun _ _ => h.ss _

theorem Fr.swap (h : Fr s J X Y) {a b : Type} (P : Matrix (Fin n) a R) (Q : Matrix (Fin n) b R) :
    cT s (cT s P * J * Q) = cT s Q * J * P := by
  rw [cT_mul, cT_mul, h.cc, h.herm, Matrix.mul_assoc]

theorem Fr.yx (h : Fr s J X Y) : cT s Y * J * X = 1 := by rw [← h.swap, h.xy, cT_one]

theorem Fr.zero (h : Fr s J X Y) {a b : Type} {P : Matrix (Fin n) a R} {Q : Matrix (Fin n) b R}
    (e : cT s P * J * Q = 0) : cT s Q * J * P = 0 := by rw [← h.swap, e, cT_zero]

theorem gram_unitary {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * J * g = J) {a b : Type} (P : Matrix (Fin n) a R)
    (Q : Matrix (Fin n) b R) : cT s (g * P) * J * (g * Q) = cT s P * J * Q := by
  conv_rhs => rw [← hg]
  simp only [cT_mul, Matrix.mul_assoc]

theorem Fr.par (h : Fr s J X Y) {g : Matrix (Fin n) (Fin n) R} (hg : cT s g * J * g = J) {B : Matrix (Fin k) (Fin k) R}
    (hB : g * X = X * B) : cT s Y * J * (g * X) = B ∧ cT s B * (cT s X * J * (g * Y)) = 1 ∧
      cT s X * J * (g * Y) * cT s B = 1 ∧ cT s X * J * g = cT s X * J * (g * Y) * (cT s X * J) := by
  have h1 : cT s B * (cT s X * J * g) = cT s X * J := by
    have := gram_unitary hg X (1 : Matrix (Fin n) (Fin n) R)
    rwa [hB, cT_mul, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s X)] at this
  have h2 : cT s B * (cT s X * J * (g * Y)) = 1 := by
    rw [← Matrix.mul_assoc (cT s X * J), ← Matrix.mul_assoc, h1, h.xy]
  have h3 := mul_eq_one_comm.1 h2
  refine ⟨by rw [hB, ← Matrix.mul_assoc, h.yx, Matrix.one_mul], h2, h3, ?_⟩
  conv_rhs => enter [2]; rw [← h1]
  rw [← Matrix.mul_assoc _ (cT s B), h3, Matrix.one_mul]

theorem Fr.symm (h : Fr s J X Y) : Fr s J Y X := ⟨h.ss, h.herm, h.yy, h.xx, h.yx⟩

theorem Fr.ext (h : Fr s J X Y) {g g' : Matrix (Fin n) (Fin n) R} (h1 : g * X = g' * X) (h2 : g * Y = g' * Y)
    (h3 : ∀ Z : Matrix (Fin n) (Fin n) R, cT s X * J * Z = 0 → cT s Y * J * Z = 0 → g * Z = g' * Z) : g = g' := by
  have := h3 (1 - X * (cT s Y * J) - Y * (cT s X * J))
    (by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.xx, h.xy]; simp)
    (by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.yy, h.yx]; simp)
  simpa only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h1, h2, Matrix.mul_one, sub_left_inj]
    using this

theorem Fr.comm (h : Fr s J X Y) {l b : Matrix (Fin n) (Fin n) R} (hl : cT s l * J * l = J)
    {B D B' D' : Matrix (Fin k) (Fin k) R} (hB : l * X = X * B) (hD : l * Y = Y * D) (hB' : b * X = X * B')
    (hD' : b * Y = Y * D') (e1 : B * B' = B' * B) (e2 : D * D' = D' * D)
    (hb : ∀ Z : Matrix (Fin n) (Fin n) R, cT s X * J * Z = 0 → cT s Y * J * Z = 0 → b * Z = Z) : b * l = l * b := by
  refine h.ext ?_ ?_ fun Z h1 h2 => ?_
  · rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hB', Matrix.mul_assoc l, hB', ← Matrix.mul_assoc l, hB,
      Matrix.mul_assoc, Matrix.mul_assoc, e1]
  · rw [Matrix.mul_assoc, hD, ← Matrix.mul_assoc, hD', Matrix.mul_assoc l, hD', ← Matrix.mul_assoc l, hD,
      Matrix.mul_assoc, Matrix.mul_assoc, e2]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, hb Z h1 h2, hb]
    · rw [← Matrix.mul_assoc, (h.par hl hB).2.2.2, Matrix.mul_assoc, h1, Matrix.mul_zero]
    · rw [← Matrix.mul_assoc, (h.symm.par hl hD).2.2.2, Matrix.mul_assoc, h2, Matrix.mul_zero]

variable (s J X) in

def eich (Z : Matrix (Fin n) (Fin k) R) (c : Matrix (Fin k) (Fin k) R) : Matrix (Fin n) (Fin n) R :=
  1 + Z * (cT s X * J) - X * (cT s Z * J) + X * c * (cT s X * J)

theorem Fr.eich_mul_of (h : Fr s J X Y) {Z : Matrix (Fin n) (Fin k) R} (c : Matrix (Fin k) (Fin k) R) {a : Type}
    {U : Matrix (Fin n) a R} (hU : cT s X * J * U = 0) : eich s J X Z c * U = U - X * (cT s Z * J * U) := by
  simp only [eich, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc _ (cT s X * J), hU, Matrix.mul_assoc X (cT s Z * J)]
  simp

theorem Fr.eich_X (h : Fr s J X Y) {Z : Matrix (Fin n) (Fin k) R} (hZ : cT s X * J * Z = 0) (c : Matrix (Fin k) (Fin k) R) :
    eich s J X Z c * X = X := by rw [h.eich_mul_of c h.xx, h.zero hZ]; simp

theorem Fr.eich_Y (h : Fr s J X Y) {Z : Matrix (Fin n) (Fin k) R} (hZ : cT s Y * J * Z = 0) (c : Matrix (Fin k) (Fin k) R) :
    eich s J X Z c * Y = Y + Z + X * c := by
  simp only [eich, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc _ (cT s X * J), h.xy, Matrix.mul_assoc X (cT s Z * J),
    h.zero hZ]
  simp

theorem Fr.eich_mul (h : Fr s J X Y) {Z₀ Z : Matrix (Fin n) (Fin k) R} (h₀ : cT s X * J * Z₀ = 0) (hZ : cT s X * J * Z = 0)
    (c₀ c : Matrix (Fin k) (Fin k) R) :
    eich s J X Z₀ c₀ * eich s J X Z c = eich s J X (Z₀ + Z) (c₀ + c - cT s Z₀ * J * Z) := by
  conv_lhs => rw [show eich s J X Z c = 1 + _ - _ + _ from rfl]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc (eich s J X Z₀ c₀), Matrix.mul_assoc X c,
    h.eich_X h₀, h.eich_mul_of c₀ hZ]
  simp only [eich, cT_add, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
  abel

theorem eich_zero : eich s J X 0 0 = 1 := by simp [eich, cT_zero]

theorem Fr.eich_unitary (h : Fr s J X Y) {Z : Matrix (Fin n) (Fin k) R} (hZ : cT s X * J * Z = 0)
    {c : Matrix (Fin k) (Fin k) R} (hc : cT s c + c + cT s Z * J * Z = 0) :
    cT s (eich s J X Z c) * J * eich s J X Z c = J := by
  have e : cT s (eich s J X Z c) * J = J * eich s J X (-Z) (cT s c) := by
    simp only [eich, cT_add, cT_sub, cT_mul, cT_one, cT_neg, h.cc, h.herm, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul,
      Matrix.sub_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [e, Matrix.mul_assoc, h.eich_mul (by rw [Matrix.mul_neg, hZ, neg_zero]) hZ, cT_neg, Matrix.neg_mul, Matrix.neg_mul,
    sub_neg_eq_add, hc, neg_add_cancel, eich_zero, Matrix.mul_one]

variable (s J X Y) in

def W1 : AddSubgroup (Matrix (Fin n) (Fin k) R) where
  carrier := {Z | cT s X * J * Z = 0 ∧ cT s Y * J * Z = 0}
  zero_mem' := by simp
  add_mem' ha hb := ⟨by rw [Matrix.mul_add, ha.1, hb.1, add_zero], by rw [Matrix.mul_add, ha.2, hb.2, add_zero]⟩
  neg_mem' ha := ⟨by rw [Matrix.mul_neg, ha.1, neg_zero], by rw [Matrix.mul_neg, ha.2, neg_zero]⟩

variable (s k) in

def W2 : AddSubgroup (Matrix (Fin k) (Fin k) R) where
  carrier := {c | cT s c = -c}
  zero_mem' := by simp [cT_zero]
  add_mem' {a b} (ha : cT s a = -a) (hb : cT s b = -b) := show cT s _ = _ by rw [cT_add, ha, hb, neg_add]
  neg_mem' {a} (ha : cT s a = -a) := show cT s _ = _ by rw [cT_neg, ha]

variable [Invertible (2 : R)]

theorem s_half : s ⅟2 = ⅟2 := by
  have : s ⅟2 * 2 = 1 := by
    have := congrArg s (invOf_mul_self (2 : R))
    rwa [map_mul, map_one, map_ofNat] at this
  exact (invOf_eq_left_inv this).symm

theorem half_add {a b : Type} (P : Matrix a b R) : (⅟2 : R) • P + (⅟2 : R) • P = P := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

def Fr.β (h : Fr s J X Y) : W1 s J X Y →+ W1 s J X Y →+ W2 s k :=
  AddMonoidHom.mk' (fun Z₀ => AddMonoidHom.mk' (fun Z =>
    ⟨(⅟2 : R) • (cT s Z.1 * J * Z₀.1 - cT s Z₀.1 * J * Z.1), show cT s _ = _ by
      rw [cT_smul, s_half, cT_sub, h.swap, h.swap, ← smul_neg, neg_sub]⟩)
    fun a b => Subtype.ext (by
      simp only [AddSubgroup.coe_add, cT_add, Matrix.add_mul, Matrix.mul_add, smul_add, smul_sub]; abel))
    fun a b => AddMonoidHom.ext fun c => Subtype.ext (by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, AddSubgroup.coe_add, cT_add, Matrix.add_mul,
        Matrix.mul_add, smul_add, smul_sub]; abel)

theorem Fr.β_val (h : Fr s J X Y) (Z₀ Z : W1 s J X Y) :
    (h.β Z₀ Z).1 = (⅟2 : R) • (cT s Z.1 * J * Z₀.1 - cT s Z₀.1 * J * Z.1) := rfl

def Fr.nMat (h : Fr s J X Y) : Heis h.β →* Matrix (Fin n) (Fin n) R where
  toFun x := eich s J X x.1.1 (x.2.1 - (⅟2 : R) • (cT s x.1.1 * J * x.1.1))
  map_one' := by
    change eich s J X 0 (0 - (⅟2 : R) • (cT s (0 : Matrix (Fin n) (Fin k) R) * J * 0)) = 1
    simp [eich_zero]
  map_mul' x y := by
    have key : ∀ (Z₀ Z : Matrix (Fin n) (Fin k) R) (c₀ c : Matrix (Fin k) (Fin k) R),
        c₀ + c + (⅟2 : R) • (cT s Z * J * Z₀ - cT s Z₀ * J * Z) - (⅟2 : R) • (cT s (Z₀ + Z) * J * (Z₀ + Z)) =
          c₀ - (⅟2 : R) • (cT s Z₀ * J * Z₀) + (c - (⅟2 : R) • (cT s Z * J * Z)) - cT s Z₀ * J * Z := fun Z₀ Z c₀ c => by
      simp only [cT_add, Matrix.add_mul, Matrix.mul_add, smul_add, smul_sub]
      have := half_add (cT s Z₀ * J * Z)
      generalize (⅟2 : R) • (cT s Z₀ * J * Z) = m at this ⊢
      rw [← this]
      abel
    rw [h.eich_mul x.1.2.1 y.1.2.1]
    exact congrArg (eich s J X (x.1.1 + y.1.1)) (key x.1.1 y.1.1 x.2.1 y.2.1)

theorem Fr.nMat_apply (h : Fr s J X Y) (x : Heis h.β) :
    h.nMat x = eich s J X x.1.1 (x.2.1 - (⅟2 : R) • (cT s x.1.1 * J * x.1.1)) := rfl

theorem Fr.decomp_inj (h : Fr s J X Y) {Z Z' : Matrix (Fin n) (Fin k) R} (hZ : cT s Y * J * Z = 0) (hZ' : cT s Y * J * Z' = 0)
    {c c' : Matrix (Fin k) (Fin k) R} (e : Y + Z + X * c = Y + Z' + X * c') : Z = Z' ∧ c = c' := by
  have e1 := congrArg (cT s Y * J * ·) e
  simp only [Matrix.mul_add, ← Matrix.mul_assoc _ X, h.yx, hZ, hZ', Matrix.one_mul] at e1
  obtain rfl := add_left_cancel e1
  exact ⟨by simpa using e, rfl⟩

theorem Fr.nMat_inj (h : Fr s J X Y) {x y : Heis h.β} (e : h.nMat x * Y = h.nMat y * Y) : x = y := by
  rw [h.nMat_apply, h.nMat_apply, h.eich_Y x.1.2.2, h.eich_Y y.1.2.2] at e
  obtain ⟨e1, e2⟩ := h.decomp_inj x.1.2.2 y.1.2.2 e
  rw [e1, sub_left_inj] at e2
  exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)

def Fr.pt (h : Fr s J X Y) (W : Matrix (Fin n) (Fin k) R) (h1 : cT s X * J * W = 1) (h2 : cT s W * J * W = 0) : Heis h.β :=
  (⟨W - Y - X * (cT s Y * J * W),
    by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, h1, h.xy, h.xx]; simp,
    by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, h.yy, h.yx]; simp⟩,
   ⟨(⅟2 : R) • (cT s Y * J * W - cT s W * J * Y), show cT s _ = _ by
      rw [cT_smul, s_half, cT_sub, h.swap, h.swap, ← smul_neg, neg_sub]⟩)

theorem Fr.nMat_pt (h : Fr s J X Y) (W : Matrix (Fin n) (Fin k) R) (h1 : cT s X * J * W = 1) (h2 : cT s W * J * W = 0) :
    h.nMat (h.pt W h1 h2) * Y = W := by
  rw [h.nMat_apply, h.eich_Y (h.pt W h1 h2).1.2.2]
  have h3 : cT s W * J * X = 1 := by rw [← h.swap, h1, cT_one]
  have e : cT s (W - Y - X * (cT s Y * J * W)) * J * (W - Y - X * (cT s Y * J * W)) =
      -(cT s Y * J * W) - cT s W * J * Y := by
    rw [cT_sub, cT_sub, cT_mul, h.swap]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc (cT s W * J * Y), ← Matrix.mul_assoc _ X, h1, h2, h3,
      h.xx, h.xy, h.yx, h.yy]
    simp
  change Y + (W - Y - X * (cT s Y * J * W)) + X * ((⅟2 : R) • (cT s Y * J * W - cT s W * J * Y) -
    (⅟2 : R) • (cT s (W - Y - X * (cT s Y * J * W)) * J * (W - Y - X * (cT s Y * J * W)))) = W
  rw [e, ← smul_sub, show cT s Y * J * W - cT s W * J * Y - (-(cT s Y * J * W) - cT s W * J * Y) =
    cT s Y * J * W + cT s Y * J * W by abel, smul_add, half_add]
  abel

end Alg

section Top

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]

instance lcMat (a b : ℕ) : LocallyCompactSpace (Matrix (Fin a) (Fin b) R) :=
  inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → R))

instance scMat (a b : ℕ) : SecondCountableTopology (Matrix (Fin a) (Fin b) R) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → R))

instance scSub {a b : ℕ} (W : AddSubgroup (Matrix (Fin a) (Fin b) R)) : SecondCountableTopology W :=
  TopologicalSpace.Subtype.secondCountableTopology (W : Set (Matrix (Fin a) (Fin b) R))

omit [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] in
theorem continuous_cT (hs : Continuous s) {a b T : Type} [TopologicalSpace T] {f : T → Matrix a b R} (hf : Continuous f) :
    Continuous fun x => cT s (f x) := (hf.matrix_map hs).matrix_transpose

omit [LocallyCompactSpace R] [SecondCountableTopology R] in
theorem isClosed_frame_annihilator : IsClosed (W1 s J X Y : Set (Matrix (Fin n) (Fin k) R)) :=
  (isClosed_eq (continuous_const.matrix_mul continuous_id) continuous_const).inter
    (isClosed_eq (continuous_const.matrix_mul continuous_id) continuous_const)

omit [LocallyCompactSpace R] [SecondCountableTopology R] in
theorem isClosed_skew_hermitian (hs : Continuous s) : IsClosed (W2 s k : Set (Matrix (Fin k) (Fin k) R)) :=
  isClosed_eq (continuous_cT hs continuous_id) continuous_neg

def scal {a b : ℕ} (W : AddSubgroup (Matrix (Fin a) (Fin b) R)) (u : Rˣ) (h : ∀ x ∈ W, u.1 • x ∈ W)
    (h' : ∀ x ∈ W, u⁻¹.1 • x ∈ W) : W ≃ₜ+ W where
  toFun x := ⟨u.1 • x.1, h _ x.2⟩
  invFun x := ⟨u⁻¹.1 • x.1, h' _ x.2⟩
  left_inv x := Subtype.ext (by simp [smul_smul])
  right_inv x := Subtype.ext (by simp [smul_smul])
  map_add' x y := Subtype.ext (smul_add _ _ _)
  continuous_toFun := (continuous_subtype_val.const_smul u.1).subtype_mk _
  continuous_invFun := (continuous_subtype_val.const_smul u⁻¹.1).subtype_mk _

def scalM (a b : ℕ) (u : Rˣ) : Matrix (Fin a) (Fin b) R ≃ₜ+ Matrix (Fin a) (Fin b) R where
  toFun x := u.1 • x
  invFun x := u⁻¹.1 • x
  left_inv x := by simp [smul_smul]
  right_inv x := by simp [smul_smul]
  map_add' x y := smul_add _ _ _
  continuous_toFun := continuous_id.const_smul u.1
  continuous_invFun := continuous_id.const_smul u⁻¹.1

@[reducible] def msMat (a b : ℕ) : MeasurableSpace (Matrix (Fin a) (Fin b) R) := borel _

attribute [local instance] msMat

local instance (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) R) := ⟨rfl⟩

omit [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] in
theorem smul_mem_frame_annihilator (c : R) (x) (hx : x ∈ W1 s J X Y) : c • x ∈ W1 s J X Y :=
  ⟨by rw [Matrix.mul_smul, hx.1, smul_zero], by rw [Matrix.mul_smul, hx.2, smul_zero]⟩

omit [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] in
theorem smul_mem_skew_hermitian {c : R} (hc : s c = c) (x) (hx : x ∈ W2 s k) : c • x ∈ W2 s k :=
  show cT s _ = _ by rw [cT_smul, hc, show cT s x = -x from hx, smul_neg]

omit [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] in
theorem s_inv {u : Rˣ} (hu : s u = u) : s u⁻¹.1 = u⁻¹.1 :=
  (Units.inv_eq_of_mul_eq_one_right (by rw [← hu, ← map_mul, Units.mul_inv, map_one])).symm

theorem haar_character_frame_annihilator (h : Fr s J X Y) [LocallyCompactSpace (W1 s J X Y)] (u : Rˣ) :
    addEquivAddHaarChar (scalM n k u) = addEquivAddHaarChar (scal (W1 s J X Y) u (smul_mem_frame_annihilator _) (smul_mem_frame_annihilator _)) *
      (addEquivAddHaarChar (scalM k k u) * addEquivAddHaarChar (scalM k k u)) := by
  rw [← GlobalTheory.T.addEquivAddHaarChar_prodCongr, ← GlobalTheory.T.addEquivAddHaarChar_prodCongr]
  let e : (W1 s J X Y × Matrix (Fin k) (Fin k) R × Matrix (Fin k) (Fin k) R) ≃ₜ+ Matrix (Fin n) (Fin k) R :=
    { toFun := fun p => p.1.1 + X * p.2.1 + Y * p.2.2
      invFun := fun U => (⟨U - X * (cT s Y * J * U) - Y * (cT s X * J * U),
        by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.xy, h.xx]; simp,
        by simp only [Matrix.mul_sub, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.yy, h.yx]; simp⟩,
        cT s Y * J * U, cT s X * J * U)
      left_inv := fun p => by
        have e1 : cT s Y * J * (p.1.1 + X * p.2.1 + Y * p.2.2) = p.2.1 := by
          simp only [Matrix.mul_add, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.yy, h.yx, p.1.2.2]; simp
        have e2 : cT s X * J * (p.1.1 + X * p.2.1 + Y * p.2.2) = p.2.2 := by
          simp only [Matrix.mul_add, ← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, h.xy, h.xx, p.1.2.1]; simp
        refine Prod.ext (Subtype.ext ?_) (Prod.ext e1 e2)
        simp only [e1, e2]
        abel
      right_inv := fun U => by simp only; abel
      map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, Matrix.mul_add]; abel
      continuous_toFun := ((continuous_subtype_val.comp continuous_fst).add
        (continuous_const.matrix_mul continuous_snd.fst)).add (continuous_const.matrix_mul continuous_snd.snd)
      continuous_invFun := (((continuous_id.sub (continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id))).sub
        (continuous_const.matrix_mul (continuous_const.matrix_mul continuous_id))).subtype_mk _).prodMk
        ((continuous_const.matrix_mul continuous_id).prodMk (continuous_const.matrix_mul continuous_id)) }
  refine GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict _ _ e.toAddMonoidHom e.toHomeomorph.isOpenEmbedding _ _ fun p => ?_
  change u.1 • (p.1.1 + X * p.2.1 + Y * p.2.2) = u.1 • p.1.1 + X * (u.1 • p.2.1) + Y * (u.1 • p.2.2)
  simp only [smul_add, Matrix.mul_smul]

theorem haar_character_skew_hermitian [Invertible (2 : R)] (hs : Continuous s) (hss : ∀ x, s (s x) = x) [LocallyCompactSpace (W2 s k)]
    (ω : Rˣ) (hω : s ω = -ω) {u : Rˣ} (hu : s u = u) :
    addEquivAddHaarChar (scalM k k u) = addEquivAddHaarChar (scal (W2 s k) u (smul_mem_skew_hermitian hu) (smul_mem_skew_hermitian (s_inv hu))) *
      addEquivAddHaarChar (scal (W2 s k) u (smul_mem_skew_hermitian hu) (smul_mem_skew_hermitian (s_inv hu))) := by
  rw [← GlobalTheory.T.addEquivAddHaarChar_prodCongr]
  have cc : ∀ P : Matrix (Fin k) (Fin k) R, cT s (cT s P) = P := fun P => Matrix.ext fun _ _ => hss _
  have hω' : s ω⁻¹.1 = -ω⁻¹.1 := by
    have : s ω⁻¹.1 * ω = -1 := by rw [← neg_neg ω.1, ← hω, mul_neg, ← map_mul, Units.inv_mul, map_one]
    rw [← mul_one (s _), ← ω.mul_inv, ← mul_assoc, this, neg_one_mul]
  let e : (W2 s k × W2 s k) ≃ₜ+ Matrix (Fin k) (Fin k) R :=
    { toFun := fun p => p.1.1 + ω.1 • p.2.1
      invFun := fun U => (⟨(⅟2 : R) • (U - cT s U), show cT s _ = _ by
          rw [cT_smul, s_half, cT_sub, cc, ← smul_neg, neg_sub]⟩,
        ⟨ω⁻¹.1 • (⅟2 : R) • (U + cT s U), show cT s _ = _ by
          rw [cT_smul, cT_smul, s_half, cT_add, cc, hω', neg_smul, add_comm]⟩)
      left_inv := fun p => by
        have e1 : cT s (p.1.1 + ω.1 • p.2.1) = -p.1.1 + ω.1 • p.2.1 := by
          rw [cT_add, cT_smul, hω, show cT s p.1.1 = -p.1.1 from p.1.2, show cT s p.2.1 = -p.2.1 from p.2.2, neg_smul_neg]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simp only [e1]
          rw [show p.1.1 + ω.1 • p.2.1 - (-p.1.1 + ω.1 • p.2.1) = p.1.1 + p.1.1 by abel, smul_add, half_add]
        · simp only [e1]
          rw [show p.1.1 + ω.1 • p.2.1 + (-p.1.1 + ω.1 • p.2.1) = ω.1 • p.2.1 + ω.1 • p.2.1 by abel, smul_add, half_add,
            smul_smul, Units.inv_mul, one_smul]
      right_inv := fun U => by
        simp only [smul_smul ω.1, Units.mul_inv, one_smul, ← smul_add]
        rw [show U - cT s U + (U + cT s U) = U + U by abel, smul_add, half_add]
      map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, smul_add]; abel
      continuous_toFun := (continuous_subtype_val.comp continuous_fst).add
        ((continuous_subtype_val.comp continuous_snd).const_smul ω.1)
      continuous_invFun := (((continuous_id.sub (continuous_cT hs continuous_id)).const_smul (⅟2 : R)).subtype_mk _).prodMk
        ((((continuous_id.add (continuous_cT hs continuous_id)).const_smul (⅟2 : R)).const_smul ω⁻¹.1).subtype_mk _) }
  refine GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict _ _ e.toAddMonoidHom e.toHomeomorph.isOpenEmbedding _ _ fun p => ?_
  change u.1 • (p.1.1 + ω.1 • p.2.1) = u.1 • p.1.1 + ω.1 • u.1 • p.2.1
  rw [smul_add, smul_comm]

theorem char_conj [Invertible (2 : R)] (h : Fr s J X Y) (hs : Continuous s) (ω : Rˣ) (hω : s ω = -ω) {u : Rˣ} (hu : s u = u)
    {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
    [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (j : H →* GL (Fin n) R)
    (hj : IsEmbedding j) (hU : ∀ p, cT s (j p).1 * J * (j p).1 = J) (hP : ∀ p, ∃ B : Matrix (Fin k) (Fin k) R, (j p).1 * X = X * B)
    (hN : ∀ x, ∃ p, (j p).1 = h.nMat x) (b : H) (bX : (j b).1 * X = u.1 • X) (bY : (j b).1 * Y = u⁻¹.1 • Y)
    (bZ : ∀ (m : ℕ) (Z : Matrix (Fin n) (Fin m) R), cT s X * J * Z = 0 → cT s Y * J * Z = 0 → (j b).1 * Z = Z)
    (φ : H ≃ₜ* H) (hφ : ∀ p, φ p = b * p * b⁻¹) :
    mulEquivHaarChar φ * addEquivAddHaarChar (scalM k k u) = addEquivAddHaarChar (scalM n k u) := by
  have : LocallyCompactSpace (W1 s J X Y) := isClosed_frame_annihilator.locallyCompactSpace
  have : LocallyCompactSpace (W2 s k) := (isClosed_skew_hermitian hs).locallyCompactSpace
  have c1 : Continuous fun Z : W1 s J X Y => Z.1 := continuous_subtype_val
  have hβ : Continuous fun p : W1 s J X Y × W1 s J X Y => h.β p.1 p.2 :=
    (((((continuous_cT hs (c1.comp continuous_snd)).matrix_mul continuous_const).matrix_mul (c1.comp continuous_fst)).sub
      (((continuous_cT hs (c1.comp continuous_fst)).matrix_mul continuous_const).matrix_mul
        (c1.comp continuous_snd))).const_smul (⅟2 : R)).subtype_mk fun p => (h.β p.1 p.2).2
  have := Heis.isTopologicalGroup h.β hβ
  have hu2 : s (u * u).1 = (u * u).1 := by rw [Units.val_mul, map_mul, hu]
  let θ₁ := scal (W1 s J X Y) u (smul_mem_frame_annihilator _) (smul_mem_frame_annihilator _)
  let θ := scal (W2 s k) u (smul_mem_skew_hermitian hu) (smul_mem_skew_hermitian (s_inv hu))
  let θ₂ := θ.trans θ
  let ψ : Heis h.β ≃ₜ* Heis h.β :=
    { toFun := fun x => (θ₁ x.1, θ₂ x.2)
      invFun := fun x => (θ₁.symm x.1, θ₂.symm x.2)
      left_inv := fun x => Prod.ext (θ₁.symm_apply_apply _) (θ₂.symm_apply_apply _)
      right_inv := fun x => Prod.ext (θ₁.apply_symm_apply _) (θ₂.apply_symm_apply _)
      map_mul' := fun x y => Prod.ext (map_add θ₁ _ _) (Subtype.ext (by
        change u.1 • u.1 • (x.2.1 + y.2.1 + (h.β x.1 y.1).1) =
          u.1 • u.1 • x.2.1 + u.1 • u.1 • y.2.1 + (h.β (θ₁ x.1) (θ₁ y.1)).1
        rw [h.β_val, h.β_val]
        change _ = _ + (⅟2 : R) • (cT s (u.1 • y.1.1) * J * (u.1 • x.1.1) - cT s (u.1 • x.1.1) * J * (u.1 • y.1.1))
        simp only [cT_smul, hu, Matrix.smul_mul, Matrix.mul_smul, smul_add, ← smul_sub, smul_comm (⅟2 : R) u.1]))
      continuous_toFun := θ₁.continuous.prodMap θ₂.continuous
      continuous_invFun := θ₁.symm.continuous.prodMap θ₂.symm.continuous }
  choose ι₀ hι₀ using hN
  have jinj : ∀ {p q}, (j p).1 = (j q).1 → p = q := fun e => hj.injective (Units.ext e)
  let ι : Heis h.β →* H := MonoidHom.mk' ι₀ fun x y => jinj (by rw [map_mul, Units.val_mul, hι₀, hι₀, hι₀, map_mul])
  have hι : ∀ x, (j (ι x)).1 = h.nMat x := hι₀
  have cn : Continuous h.nMat := by
    have d1 : Continuous fun x : Heis h.β => x.1.1 := c1.comp continuous_fst
    have d2 : Continuous fun x : Heis h.β => x.2.1 := continuous_subtype_val.comp continuous_snd
    exact ((continuous_const.add (d1.matrix_mul continuous_const)).sub
      (continuous_const.matrix_mul ((continuous_cT hs d1).matrix_mul continuous_const))).add
      ((continuous_const.matrix_mul (d2.sub ((((continuous_cT hs d1).matrix_mul continuous_const).matrix_mul d1).const_smul
        (⅟2 : R)))).matrix_mul continuous_const)
  have cι : Continuous ι := hj.continuous_iff.2 (Units.continuous_iff.2
    ⟨cn.congr fun x => (hι x).symm, (cn.comp continuous_inv).congr fun x => by
      rw [Function.comp, Function.comp, ← map_inv, ← map_inv, hι]⟩)
  have cj : Continuous fun p => (j p).1 := Units.continuous_val.comp hj.continuous
  let B : H → Matrix (Fin k) (Fin k) R := fun p => cT s Y * J * ((j p).1 * X)
  have hB : ∀ p, (j p).1 * X = X * B p := fun p => by
    obtain ⟨B', e⟩ := hP p
    rw [show B p = B' from (h.par (hU p) e).1, e]
  let W : H → Matrix (Fin n) (Fin k) R := fun p => (j p).1 * Y * cT s (B p)
  have cW : Continuous W := (cj.matrix_mul continuous_const).matrix_mul
    (continuous_cT hs (continuous_const.matrix_mul (cj.matrix_mul continuous_const)))
  have W1' : ∀ p, cT s X * J * W p = 1 := fun p => by rw [← Matrix.mul_assoc, (h.par (hU p) (hB p)).2.2.1]
  have W2' : ∀ p, cT s (W p) * J * W p = 0 := fun p => by
    simp only [W]
    rw [Matrix.mul_assoc (j p).1, gram_unitary (hU p), cT_mul, Matrix.mul_assoc _ (cT s Y), ← Matrix.mul_assoc,
      Matrix.mul_assoc _ _ Y, h.yy]
    simp
  let π : H → Heis h.β := fun p => h.pt (W p) (W1' p) (W2' p)
  have hπ : ∀ p, h.nMat (π p) * Y = W p := fun p => h.nMat_pt _ _ _
  have cπ : Continuous π :=
    (((cW.sub continuous_const).sub (continuous_const.matrix_mul (continuous_const.matrix_mul cW))).subtype_mk _).prodMk
      ((((continuous_const.matrix_mul cW).sub (((continuous_cT hs cW).matrix_mul continuous_const).matrix_mul
        continuous_const)).const_smul (⅟2 : R)).subtype_mk _)
  have nX : ∀ x, h.nMat x * X = X := fun x => h.eich_X x.1.2.1 _
  have Beq : ∀ p B', (j p).1 * X = X * B' → B p = B' := fun p B' e => (h.par (hU p) e).1
  have bb : (j b).1 * (j b⁻¹).1 = 1 := by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have bb' : (j b⁻¹).1 * (j b).1 = 1 := mul_eq_one_comm.1 bb
  have bX' : (j b⁻¹).1 * X = u⁻¹.1 • X := by
    have := congrArg (fun M => u⁻¹.1 • (j b⁻¹).1 * M) bX
    simpa [← Matrix.mul_assoc, bb', smul_smul] using this.symm
  have bY' : (j b⁻¹).1 * Y = u.1 • Y := by
    have := congrArg (fun M => u.1 • (j b⁻¹).1 * M) bY
    simpa [← Matrix.mul_assoc, bb', smul_smul] using this.symm
  have bJ : ∀ Z : Matrix (Fin n) (Fin k) R, cT s Z * J * (j b⁻¹).1 = cT s ((j b).1 * Z) * J := fun Z => by
    rw [← gram_unitary (hU b) Z, bb, Matrix.mul_one]
  have hφι : ∀ x, φ (ι x) = ι (ψ x) := fun x => jinj (by
    rw [hφ, map_mul, map_mul, Units.val_mul, Units.val_mul, hι, hι, h.nMat_apply, h.nMat_apply]
    change _ = eich s J X (u.1 • x.1.1) (u.1 • u.1 • x.2.1 - (⅟2 : R) • (cT s (u.1 • x.1.1) * J * (u.1 • x.1.1)))
    simp only [eich, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub (j b).1, Matrix.sub_mul _ _ (j b⁻¹).1, Matrix.mul_one, bb,
      ← Matrix.mul_assoc (j b).1, bX, bZ _ _ x.1.2.1 x.1.2.2, cT_smul, hu,
      Matrix.smul_mul, Matrix.mul_smul, smul_comm (⅟2 : R) u.1, ← smul_sub]
    have e1 : cT s X * J * (j b⁻¹).1 = u.1 • (cT s X * J) := by rw [bJ, bX, cT_smul, hu, Matrix.smul_mul]
    have e2 : cT s x.1.1 * J * (j b⁻¹).1 = cT s x.1.1 * J := by rw [bJ, bZ _ _ x.1.2.1 x.1.2.2]
    rw [Matrix.mul_assoc x.1.1 (cT s X * J), Matrix.mul_assoc X (cT s x.1.1 * J),
      Matrix.mul_assoc _ (cT s X * J) (j b⁻¹).1, e1, e2]
    simp only [Matrix.mul_smul])
  have h1 : ∀ p, π (φ p) = ψ (π p) := fun p => h.nMat_inj (by
    have e : B (φ p) = B p := Beq _ _ (by
      rw [hφ, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, bX', Matrix.mul_smul, Matrix.mul_assoc, hB,
        ← Matrix.mul_assoc, bX, Matrix.smul_mul, smul_smul, Units.inv_mul, one_smul])
    rw [hπ, ← hι, ← hφι, hφ (ι _), map_mul, map_mul, Units.val_mul, Units.val_mul, hι, Matrix.mul_assoc, bY', Matrix.mul_smul,
      Matrix.mul_assoc, hπ]
    simp only [W]
    rw [e, hφ, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc _ _ Y, bY']
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc])
  have key := char_eq_of_retract ι cι π cπ (fun x p => h.nMat_inj (by
    have e : B (ι x * p) = B p := Beq _ _ (by
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hι, nX])
    rw [hπ, map_mul, Matrix.mul_assoc, hπ]
    simp only [W]
    rw [e, map_mul, Units.val_mul, hι]
    simp only [Matrix.mul_assoc])) φ ψ h1 (fun p => by
    rw [h1, ← hφι, ← map_inv φ, ← map_mul φ, hφ, mul_inv_eq_iff_eq_mul]
    apply jinj
    rw [map_mul j b, map_mul j _ b, Units.val_mul, Units.val_mul]
    refine h.comm (hU _) (hB _) (D := cT s X * J * ((j p).1 * Y)) ?_ (B' := u.1 • 1) (D' := u⁻¹.1 • 1) (by simp [bX])
      (by simp [bY]) (by simp) (by simp) (bZ n)
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, ← map_inv, hι]
    have e : (j p).1 * Y = h.nMat (π p) * Y * (cT s X * J * ((j p).1 * Y)) := by
      rw [hπ, Matrix.mul_assoc, (h.par (hU p) (hB p)).2.1, Matrix.mul_one]
    conv_lhs => rw [e]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc _ (h.nMat _) Y, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul])
  rw [key, Heis.char_eq h.β hβ ψ θ₁ θ₂ fun _ => rfl, haar_character_frame_annihilator h u, addEquivAddHaarChar_trans, ← haar_character_skew_hermitian hs h.ss ω hω hu,
    mul_assoc]

end Top

end CompanionTheory.ThKR.Sieg

end
end

section
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)
open CompanionTheory.ThKEst CompanionTheory.ThKEst.Sieg

namespace CompanionTheory.ThKR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}

variable (σ J X Y) in

structure IsTorus (a : (Fin r → ℝ) → GAd σ J) : Prop where
  add : ∀ s t, a (s + t) = a s * a t
  cont : Continuous a
  tor : ∀ t, IsTorusElt σ J X Y (fun i => Real.exp (t i)) (a t)
  onX : ∀ t, (matHom _ σ J (a t)).1 * adMat F X = adMat F X * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (t i)))
  onY : ∀ t, (matHom _ σ J (a t)).1 * adMat F Y = adMat F Y * diagonal (fun i => algebraMap (AF F) (AE F E) (rId F (-t i)))
  onV : ∀ t, ∀ z : Fin n → E, (cT (σ : E →+* E) X * J) *ᵥ z = 0 → (cT (σ : E →+* E) Y * J) *ᵥ z = 0 →
    (matHom _ σ J (a t)).1 *ᵥ incV F z = incV F z

theorem mul_mem_minPar {p q : GAd σ J} (hp : p ∈ minPar σ J X) (hq : q ∈ minPar σ J X) : p * q ∈ minPar σ J X :=
  mul_mem_minimal_parabolic hp hq

theorem inv_mem_minPar (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) {p : GAd σ J}
    (hp : p ∈ minPar σ J X) : p⁻¹ ∈ minPar σ J X :=
  inv_mem_minimal_parabolic h hJ hW hp

variable (X) in

def minParSub (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) : Subgroup (GAd σ J) where
  carrier := minPar σ J X
  one_mem' := one_mem_minPar σ J X
  mul_mem' := mul_mem_minPar
  inv_mem' := inv_mem_minPar h hJ hW

theorem IsTorus.mem {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (t : Fin r → ℝ) : a t ∈ minPar σ J X :=
  ⟨_, Matrix.blockTriangular_diagonal _, ha.onX t⟩

def IsTorus.sub {a : (Fin r → ℝ) → GAd σ J} (ha : IsTorus σ J X Y a) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) (t : Fin r → ℝ) : minParSub X h hJ hW :=
  ⟨a t, ha.mem t⟩

end CompanionTheory.ThKR

end
end
