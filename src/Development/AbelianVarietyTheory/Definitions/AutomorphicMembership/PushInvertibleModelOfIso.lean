import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Formalism.LocalToGlobal.LatticeGeometry.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ChiGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInNormalAt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRescale
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubrings
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueIndependentNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleValuationUnitOfFunctorial
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamUnit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.FamHomogOfHomog
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleValuationUnitOfFunctorialStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaPowAndDegree
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonemptyRingHomComplex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaAndKeyCore
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyPow GlobalTheory.KeyCl

noncomputable section
namespace GlobalTheory.LocM

structure NgC (g : ℕ) : Type where

  τ : Matrix (Fin g) (Fin g) ℂ
  symm : τ.IsSymm
  pos : (τ.map Complex.im).PosDef

  a : Fin g → ℂ

  b : Fin g → ℂ
  half : charHalf g a b

namespace NgC

variable {g : ℕ}

def base (g : ℕ) (a b : Fin g → ℂ) (h : charHalf g a b) : NgC g :=
  ⟨_, (TorusAlg.hypotheses_inhabited.1 g 0 Matrix.isSymm_zero).1,
    (TorusAlg.hypotheses_inhabited.1 g 0 Matrix.isSymm_zero).2, a, b, h⟩

instance (g : ℕ) : Nonempty (NgC g) := ⟨base g 0 0 ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩⟩

def Y (z : NgC g) : Matrix (Fin g) (Fin g) ℝ := z.τ.map Complex.im

def Frame (z : NgC g) (x : KeyIn ℂ) : Prop :=
  ∃ h : x.P.g = g, NormalAt x (z.τ.submatrix (Fin.cast h) (Fin.cast h)) 1
    (fun i => z.a (i.cast h)) (fun i => z.b (i.cast h)) 1

def Lies (z : NgC g) (x : KeyIn ℂ) : Prop := KeyEq.Nrm x z.τ z.a z.b

theorem Frame.lies {z : NgC g} {x : KeyIn ℂ} (h : z.Frame x) : z.Lies x := by
  obtain ⟨e, h⟩ := h
  exact ⟨e, 1, 1, one_ne_zero, h⟩

theorem exists_frame (hg : 1 ≤ g) (z : NgC g) : ∃ x : KeyIn ℂ, z.Frame x :=
  KeyOfPeriod.exists_keyIn_normalAt thetaUnifAV_all torusAlgebraic_holds g z.τ z.a z.b hg z.symm z.pos z.half


def cubSq (z : NgC g) (w : Fin g → ℂ) : ℝ :=
  ‖thetaChar z.τ z.a z.b w‖ ^ 2 *
    Real.exp (-2 * Real.pi * ((fun i => (w i).im) ⬝ᵥ (z.Y)⁻¹.mulVec fun i => (w i).im))

def thetaSq (z : NgC g) : ℝ :=
  ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
    z.cubSq ((fun i => (p (.inl i) : ℂ)) + z.τ.mulVec (fun i => (p (.inr i) : ℂ)))

def lieGram (z : NgC g) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i j => Real.pi * hermForm ((z.Y)⁻¹.map fun x : ℝ => (x : ℂ))
    (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (Pi.single j (2 * Real.pi * Complex.I)⁻¹)

def etaSq (z : NgC g) : ℝ := (z.lieGram.det.re)⁻¹

theorem det_Y_pos (z : NgC g) : 0 < z.Y.det := z.pos.det_pos

theorem thetaSq_eq (z : NgC g) : z.thetaSq = (Real.sqrt (2 ^ g * z.Y.det))⁻¹ := by
  have ha : z.a = fun i => (((z.a i).re : ℝ) : ℂ) := (TorusAlg.ofRealVec_re z.half.1).symm
  have hb : z.b = fun i => (((z.b i).re : ℝ) : ℂ) := (TorusAlg.ofRealVec_re z.half.2).symm
  refine Eq.trans ?_ (ThetaNorm.integral_norm_sq_thetaChar g z.τ (fun i => (z.a i).re) (fun i => (z.b i).re)
    z.symm z.pos)
  rw [← ha, ← hb, thetaSq]
  congr 1
  funext p
  have e : (fun i => (((fun i => (p (.inl i) : ℂ)) + z.τ.mulVec (fun i => (p (.inr i) : ℂ))) i).im) =
      z.Y.mulVec fun i => p (.inr i) := by
    funext i
    simp [Y, Matrix.mulVec, dotProduct]
  rw [cubSq, e, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ z.det_Y_pos.ne'.isUnit, Matrix.one_mulVec,
    dotProduct_comm]
  rfl

theorem lieGram_eq (z : NgC g) :
    z.lieGram = (((4 * Real.pi)⁻¹ • (z.Y)⁻¹ : Matrix (Fin g) (Fin g) ℝ)).map fun x : ℝ => (x : ℂ) := by
  ext i j
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e : star (Pi.single j (2 * Real.pi * Complex.I : ℂ)⁻¹ : Fin g → ℂ) =
      Pi.single j (-(2 * Real.pi * Complex.I : ℂ)⁻¹) := by
    funext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  simp only [lieGram, Matrix.of_apply, hermForm, e, single_dotProduct, Matrix.mulVec_single, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp
  field_simp
  simp
  ring

theorem etaSq_eq (z : NgC g) : z.etaSq = (4 * Real.pi) ^ g * z.Y.det := by
  have e : z.lieGram.det = ((((4 * Real.pi)⁻¹ • (z.Y)⁻¹ : Matrix (Fin g) (Fin g) ℝ)).det : ℝ) := by
    rw [lieGram_eq]
    exact (RingHom.map_det Complex.ofRealHom _).symm
  rw [etaSq, e, Complex.ofReal_re, Matrix.det_smul, Matrix.det_nonsing_inv, Fintype.card_fin, Ring.inverse_eq_inv',
    mul_inv, inv_inv, inv_pow, inv_inv]

theorem thetaSq_pos (z : NgC g) : 0 < z.thetaSq := by
  have := z.det_Y_pos
  rw [thetaSq_eq]; positivity

theorem etaSq_pos (z : NgC g) : 0 < z.etaSq := by
  have := z.det_Y_pos
  have := Real.pi_pos
  rw [etaSq_eq]; positivity

theorem thetaSq_mul_sqrt_etaSq (z : NgC g) : z.thetaSq * Real.sqrt z.etaSq = Real.sqrt ((2 * Real.pi) ^ g) := by
  have := z.det_Y_pos
  have := Real.pi_pos
  rw [thetaSq_eq, etaSq_eq, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
  congr 1
  rw [show (4 * Real.pi) ^ g = 2 ^ g * (2 * Real.pi) ^ g by rw [← mul_pow]; congr 1; ring]
  field_simp

end NgC

structure IsKF (g c : ℕ) (κ : Rule) : Prop where
  homog : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
    (M : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
    (∀ i, IsLieComb (M i) v (v' i)) →
    a ^ (2 * c) * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ c * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩
  funct : Funct κ
  unitSp : UnitSp κ
  off : ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), x.P.g ≠ g → κ K x = 1

namespace IsKF

variable {g c : ℕ} {κ κ' : Rule}

theorem famUnit (h : IsKF g c κ) : FamUnit κ := KeyFamUnit.famUnit κ h.funct h.unitSp

theorem valUnit (h : IsKF g c κ) : ValUnit κ := KeyValUnit.valUnit κ h.funct h.unitSp


theorem value_normalAt (h : IsKF g c κ) (x : KeyIn ℂ) (hx : x.P.g = g) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c₀ : ℂ} (hc : c₀ ≠ 0) (hM : M.det ≠ 0) (hN : NormalAt x τ M a b c₀) (t : ℂ)
    (ht : ∀ (y : KeyIn ℂ) (e : y.P.g = x.P.g), NormalAt y (τ.submatrix (Fin.cast e) (Fin.cast e)) 1
      (fun i => a (i.cast e)) (fun i => b (i.cast e)) 1 → (κ ℂ y : ℂ) = t) :
    c₀ ^ (2 * c) * (κ ℂ x : ℂ) = M.det ^ c * t := by
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, hN₀, e₁, hMv⟩ := KeyConst.exists_rescale P hg rig hr th hth v hv τ M _ _ c₀ hc hM hN
  rw [← ht ⟨P, hg, rig, hr, th₀, hth₀, v₀, hv₀⟩ rfl hN₀]
  exact h.homog ℂ P hg rig hr _ hth₀ v₀ hv₀ th hth v hv c₀ M hx e₁ hMv

theorem ext (h : IsKF g c κ) (h' : IsKF g c κ') (f : NgC g → ℂˣ)
    (hf : ∀ (z : NgC g) x, z.Frame x → κ ℂ x = f z) (hf' : ∀ (z : NgC g) x, z.Frame x → κ' ℂ x = f z) : κ = κ' := by
  funext K _ _ x
  by_cases hx : x.P.g = g
  swap
  · rw [h.off K x hx, h'.off K x hx]
  obtain ⟨K₀, x₀, hK₀, hx₀⟩ := (KeyCountableDescent.keyIn_descends_countable firstFiveLaws.1).2 K x
  obtain ⟨σ⟩ := KeyRuleUnique.nonempty_ringHom_complex K₀
  obtain ⟨y, hy⟩ := exists_keyPB_ring x₀ σ
  have hyg : y.P.g = g := (KeyGalDesc.g_eq hy).trans ((KeyGalDesc.g_eq hx₀).symm.trans hx)
  subst hyg
  obtain ⟨⟨τ, M, a, b, c₀, hab, hc, hM, hN⟩, -⟩ := KeyNormalExists.exists_normalAt thetaUnifAV_all y
  let z : NgC y.P.g := ⟨τ, hN.mem_siegelH.1, hN.mem_siegelH.2, a, b, hab⟩
  have e : (κ ℂ y : ℂ) = κ' ℂ y := by
    refine mul_left_cancel₀ (pow_ne_zero (2 * c) hc) ?_
    rw [h.value_normalAt y rfl hc hM hN (f z) fun w e hw => congrArg Units.val (hf z w ⟨e, hw⟩),
      h'.value_normalAt y rfl hc hM hN (f z) fun w e hw => congrArg Units.val (hf' z w ⟨e, hw⟩)]
  rw [h.funct K₀ ℂ σ x₀ y hy, h'.funct K₀ ℂ σ x₀ y hy] at e
  apply Units.ext
  rw [h.funct K₀ K _ x₀ x hx₀, h'.funct K₀ K _ x₀ x hx₀, σ.injective e]


end IsKF

open Classical in

def cutRule (g : ℕ) (s : ℤˣ) (κ : Rule) : Rule := fun K _ _ x =>
  if x.P.g = g then Units.map (Int.castRingHom K).toMonoidHom s * κ K x else 1

theorem isKF_cutRule {g c : ℕ} (s : ℤˣ) {κ : Rule}
    (hH : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (M : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ (2 * c) * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ c * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩)
    (hF : Funct κ) (hU : UnitSp κ) : IsKF g c (cutRule g s κ) where
  homog K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂ := by
    simp only [cutRule, if_pos hP, Units.val_mul]
    rw [mul_left_comm, hH K P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂, mul_left_comm]
  funct K K' _ _ _ _ f x x' h := by
    simp only [cutRule, KeyGalDesc.g_eq h]
    split_ifs
    · simp [hF K K' f x x' h]
    · simp
  unitSp R K _ _ _ _ _ _ _ x xK h := by
    by_cases hx : x.P.g = g
    · obtain ⟨u, hu, hk⟩ := hU R K x xK h
      refine ⟨Units.map (Int.castRingHom R).toMonoidHom s * u, ?_, fun k _ _ r xk hr hxk => ?_⟩
      · simp [cutRule, KeyGalDesc.g_eq h, hx, hu]
      · simp [cutRule, KeyGalDesc.g_eq hxk, hx, hk k r xk hr hxk]
    · exact ⟨1, by simp [cutRule, KeyGalDesc.g_eq h, hx],
        fun k _ _ r xk hr hxk => by simp [cutRule, KeyGalDesc.g_eq hxk, hx]⟩
  off K _ _ x hx := if_neg hx

structure KF (g c : ℕ) : Type where

  val : NgC g → ℂˣ
  ex : ∃ κ : Rule, IsKF g c κ ∧ ∀ (z : NgC g) (x : KeyIn ℂ), z.Frame x → κ ℂ x = (val z)⁻¹
  zero : g = 0 → ∀ z, val z = 1 ∨ val z = -1

namespace KF

variable {g c : ℕ} (kf : KF g c)

def rule : Rule := kf.ex.choose

theorem isKF : IsKF g c kf.rule := kf.ex.choose_spec.1

theorem rule_frame {z : NgC g} {x : KeyIn ℂ} (h : z.Frame x) : kf.rule ℂ x = (kf.val z)⁻¹ :=
  kf.ex.choose_spec.2 z x h


@[ext] theorem ext {kf kf' : KF g c} (h : kf.val = kf'.val) : kf = kf' := by
  cases kf; cases kf'; cases h; rfl


def coef (K : Type) [Field K] [CharZero K] (x : KeyIn K) : Kˣ := (kf.rule K x)⁻¹

def norm (z : NgC g) : ℝ := ‖(kf.val z : ℂ)‖ / (z.thetaSq ^ c * Real.sqrt z.etaSq ^ c)

theorem norm_pos (z : NgC g) : 0 < kf.norm z := by
  have := z.thetaSq_pos
  have := z.etaSq_pos
  exact div_pos (norm_pos_iff.2 (kf.val z).ne_zero) (by positivity)

theorem norm_eq_div (z : NgC g) : kf.norm z = ‖(kf.val z : ℂ)‖ / Real.sqrt ((2 * Real.pi) ^ g) ^ c := by
  rw [norm, ← mul_pow, z.thetaSq_mul_sqrt_etaSq]

theorem norm_eq (z : NgC g) :
    kf.norm z = ‖(kf.val z : ℂ)‖ * Real.exp (c * g * (-(1 / 2) * Real.log (2 * Real.pi))) := by
  have hp : 0 < 2 * Real.pi := by have := Real.pi_pos; positivity
  rw [norm_eq_div, div_eq_mul_inv]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_mul hp.le,
    ← Real.rpow_neg hp.le, Real.rpow_def_of_pos hp]
  congr 1
  ring


def sign (s : ℤˣ) : KF g c where
  val z := Units.map (Int.castRingHom ℂ).toMonoidHom s * kf.val z
  ex := ⟨cutRule g s kf.rule, isKF_cutRule s kf.isKF.homog kf.isKF.funct kf.isKF.unitSp, fun z x h => by
    rw [cutRule, if_pos h.1, kf.rule_frame h]
    rcases Int.units_eq_one_or s with rfl | rfl <;> ext <;> simp⟩
  zero h z := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases kf.zero h z with e | e <;> rw [e] <;>
      [left; right; right; left] <;> ext <;> simp

theorem sign_neg_one_ne : kf.sign (-1) ≠ kf := fun h => by
  obtain ⟨z⟩ : Nonempty (NgC g) := inferInstance
  have e : (-1 : ℂ) * kf.val z = kf.val z := by simpa [sign] using congrArg (fun k : KF g c => (k.val z : ℂ)) h
  exact (kf.val z).ne_zero (by linear_combination (-1 / 2 : ℂ) * e)

def ofRule (N : ℕ → ℕ) (κ : Rule) (hH : Homog N κ) (hF : Funct κ) (hU : UnitSp κ) (hT : ThetaOne κ) (g : ℕ) :
    KF g (4 * N g) where
  val _ := 1
  ex := ⟨cutRule g 1 κ, isKF_cutRule 1 (fun K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂ => by
      subst hP
      rw [show 2 * (4 * N P.g) = 8 * N P.g by ring]
      exact hH K P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂) hF hU, fun z x h => by
    obtain ⟨e, h⟩ := h
    obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (normalAt_one_iff x _ _ _).1 h
    rw [cutRule, if_pos e, hT x u _ _ _ h₁ h₂ (fun i => z.half.1 _) (fun i => z.half.2 _) h₃ h₄ h₅ h₆]
    simp⟩
  zero _ _ := Or.inl rfl


end KF

def ngTrue : Formalism.L2.Geo.NgPkg where
  NgC := NgC
  NgC_ne _ := inferInstance
  KF := KF
  kfNorm kf z := kf.norm z




theorem exists_kf_four (g : ℕ) : ∃ kf : KF g 4, ∀ z, kf.val z = 1 := by
  obtain ⟨κ, h₁, h₂, h₃, h₄, -⟩ := keyFormula_iff.1 keyFormula_and_keyCore.1
  exact ⟨KF.ofRule (fun _ => 1) κ h₁ h₂ h₃ h₄ g, fun _ => rfl⟩


example : NgC.base 1 0 0 ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩ ≠
    NgC.base 1 (fun _ => 1 / 2) (fun _ => 1 / 2) ⟨fun _ => Or.inr rfl, fun _ => Or.inr rfl⟩ := fun h => by
  simpa [NgC.base] using congrFun (congrArg NgC.a h) 0

example (a b : Fin 1 → ℂ) (h : charHalf 1 a b) : (NgC.base 1 a b h).etaSq = 4 * Real.pi := by
  simp [NgC.etaSq_eq, NgC.Y, NgC.base]

example (g : ℕ) : ∃ kf kf' : KF g 4, kf ≠ kf' ∧ ∀ z, kf.norm z = ((2 * Real.pi) ^ (2 * g))⁻¹ := by
  obtain ⟨kf, h⟩ := exists_kf_four g
  refine ⟨kf, kf.sign (-1), kf.sign_neg_one_ne.symm, fun z => ?_⟩
  have := Real.pi_pos
  rw [kf.norm_eq_div, h z, Units.val_one, norm_one, one_div, show 4 = 2 * 2 from rfl, pow_mul,
    Real.sq_sqrt (by positivity), ← pow_mul, mul_comm g 2]

end GlobalTheory.LocM
end
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.FlagMod (GChart thUnit thRat detChg pushPP detOm detLie de ev)
open GlobalTheory.Reg (MChart)
open GlobalTheory.LB (toMod)

namespace GlobalTheory.LocM

section OneModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Transport

variable (Y : Model Xo c β) {X : Scheme.{0}} (π : X ⟶ Y.X) [IsIso π]

def genInv : pullback Y.s (spMap β) ⟶ pullback (π ≫ Y.s) (spMap β) :=
  pullback.map _ _ _ _ (inv π) (𝟙 _) (𝟙 _) (by simp) (by simp)

instance isIso_genInv : IsIso (genInv Y π) := by unfold genInv; infer_instance

theorem genInv_fst : genInv Y π ≫ pullback.fst _ _ ≫ π = pullback.fst _ _ := by
  rw [genInv, pullback.lift_fst_assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem genInv_snd : genInv Y π ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [genInv, pullback.lift_snd, Category.comp_id]

theorem exists_sabMap_genInv {t : SAB H X} (m : SABMap t Y.t π) :
    ∃ n : SABMap Y.oF.t t ((Y.jQ ≫ genInv Y π) ≫ pullback.fst _ _), n.φ ≫ m.φ = Y.m.φ := by
  have e : ((Y.jQ ≫ genInv Y π) ≫ pullback.fst _ _) ≫ π = Y.jQ ≫ pullback.fst _ _ := by
    simp only [Category.assoc, genInv_fst]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap Y.oF.t Y.t (((Y.jQ ≫ genInv Y π) ≫ pullback.fst _ _) ≫ π), n'.φ = Y.m.φ := by
    rw [e]; exact ⟨Y.m, rfl⟩
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n'
  exact ⟨n, hn.symm.trans hn'⟩

@[reducible] def modelOfIso (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (t : SAB H X) (m : SABMap t Y.t π) :
    Model Xo c β where
  X := X
  s := π ≫ Y.s
  normal := hn
  proj := by
    obtain ⟨n, i, hi, e⟩ := Y.proj
    exact ⟨n, π ≫ i, inferInstance, by rw [Category.assoc, e]⟩
  flat := have := Y.flat; inferInstance
  jQ := Y.jQ ≫ genInv Y π
  jQ_over := by rw [Category.assoc, genInv_snd, Y.jQ_over]
  jQ_open := have := Y.jQ_open; inferInstance
  jQ_dense := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (genInv Y π).surjective.denseRange.comp Y.jQ_dense (genInv Y π).continuous
  t := t
  oF := Y.oF
  m0 := Y.m0
  m := (exists_sabMap_genInv Y π m).choose
  ab_gen := by
    ext y
    obtain ⟨y, rfl⟩ := (genInv Y π).surjective y
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne Y.t.semi m.cart.1, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply, genInv_fst, ← Set.mem_preimage, Y.ab_gen]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, Scheme.Hom.comp_apply _ _ _⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (genInv Y π).homeomorph.injective ((Scheme.Hom.comp_apply _ _ _).symm.trans hx)⟩

theorem modelOfIso_j (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (t : SAB H X) (m : SABMap t Y.t π) :
    (modelOfIso Y π hn t m).j ≫ π = Y.j := by
  simp only [Model.j, Category.assoc, genInv_fst]

theorem pushInvertible_modelOfIso (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (t : SAB H X) (m : SABMap t Y.t π)
    (hD : GlobalTheory.Models.IsDedFrac β) (hY : PushInvertible Y.t.G Y.t.PP.L) : PushInvertible t.G t.PP.L := by
  obtain ⟨l₁, l₂, l₃, -, -⟩ := GlobalTheory.firstFiveLaws
  let C := modelOfIso Y π hn t m
  exact GlobalTheory.PushInv.pushInvertible_of_model l₁ l₂ l₃ E H Dw l _ _ _ _ _ _ Y.oF _ β
    ⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, C.m, C.ab_gen⟩ hD
    ((GlobalTheory.AbLocusPull.abLocus_sections_pull _ _ π Y.t.G t.G m.φ Y.t.semi m.cart).2 _ _ Y.t.PP.isLB t.PP.isLB
      (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) fun x => by
        obtain ⟨V, hV, θ, hθ, -, nz⟩ := hY x
        exact ⟨V, hV, θ, hθ, nz⟩)

end Transport

variable {Y : Model Xo c β}

def pushMod {X : Scheme.{0}} (t : SAB H X) : X.Modules := (Scheme.Modules.pushforward t.G.hom).obj (toMod t.PP.L)

def thetaSec (M : GChart Y) : Γ(pushMod Y.t, M.U) := GlobalTheory.LB.mkSec M.θ M.θ_mem

theorem isFrame_thetaSec (M : GChart Y) : GlobalTheory.LB.IsFrame (thetaSec M) := fun V h => by
  rw [Function.bijective_iff_existsUnique]
  intro s
  refine (existsUnique_congr fun a => ?_).1 (M.gen V h _ (GlobalTheory.LB.coord_mem (L := Y.t.PP.L) s))
  exact ⟨fun e => GlobalTheory.LB.sec_ext (L := Y.t.PP.L) fun i => (e i).symm,
    fun e i => (congrArg (fun s => GlobalTheory.LB.coord (L := Y.t.PP.L) s i) e).symm⟩

theorem thetaSec_change (M M' : GChart Y) :
    (pushMod Y.t).presheaf.map (homOfLE (inf_le_right : M.U ⊓ M'.U ≤ M'.U)).op (thetaSec M') =
      thRat M M' • (pushMod Y.t).presheaf.map (homOfLE (inf_le_left : M.U ⊓ M'.U ≤ M.U)).op (thetaSec M) :=
  GlobalTheory.LB.sec_ext (L := Y.t.PP.L) fun i => (M.gen _ inf_le_left _
    (GlobalTheory.ModelChart.res_mem_secOn _ (Y.t.G.hom.preimage_mono inf_le_right) M'.θ_mem)).exists.choose_spec i

theorem ofFrames_thetaSec : GlobalTheory.LB.ofFrames (fun M : GChart Y => isFrame_thetaSec M) = pushPP Y := by
  unfold pushPP GlobalTheory.LB.ofFrames
  congr 1
  funext M M'
  refine Units.ext ?_
  have e := GlobalTheory.LB.resG_ofFrames_g (fun M : GChart Y => isFrame_thetaSec M) M M' le_rfl
  rw [GlobalTheory.LB.resG_self] at e
  exact e.trans ((isFrame_thetaSec M).repr_eq _ (thetaSec_change M M').symm)

theorem nonempty_pushMod_iso (h : (pushPP Y).IsLB) : Nonempty (pushMod Y.t ≅ toMod (pushPP Y)) :=
  ofFrames_thetaSec (Y := Y) ▸ ⟨GlobalTheory.LB.ofFramesIso (fun M : GChart Y => isFrame_thetaSec M) h.cover⟩

theorem isVB_pushMod (h : (pushPP Y).IsLB) : GlobalTheory.VB.IsVB (pushMod Y.t) 1 :=
  (GlobalTheory.VB.isVB_toMod h).of_iso (nonempty_pushMod_iso h).some.symm

def keyUnit (k : ℕ) (M M' : GChart Y) : Γ(Y.X, M.U ⊓ M'.U)ˣ :=
  (thUnit M M')⁻¹ ^ (2 * k) * detChg M.toMChart M'.toMChart ^ k

theorem thRat_pow_mul_keyUnit (k : ℕ) (M M' : GChart Y) :
    thRat M M' ^ (2 * k) * (keyUnit k M M').val = (detChg M.toMChart M'.toMChart).val ^ k := by
  have : thUnit M M' ^ (2 * k) * keyUnit k M M' = detChg M.toMChart M'.toMChart ^ k := by
    simp only [keyUnit, inv_pow, mul_inv_cancel_left]
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, GlobalTheory.FlagMod.thUnit_val] using congrArg Units.val this

def keyLB (Y : Model Xo c β) (k : ℕ) : LB Y.X := ⟨GChart Y, fun M => M.U, keyUnit k⟩

theorem gm_keyUnit (k : ℕ) (M M' : GChart Y) (y : Y.X) :
    gm (𝟙 Y.X) y _ (keyUnit k M M') =
      (gm (𝟙 Y.X) y _ (thUnit M M'))⁻¹ ^ (2 * k) * gm (𝟙 Y.X) y _ (detChg M.toMChart M'.toMChart) ^ k := by
  rw [keyUnit, map_mul, map_pow, map_pow, map_inv]

section Cover

variable [IsNoetherianRing O] (hP : PushInvertible Y.t.G Y.t.PP.L)
include hP

theorem isLB_keyLB (k : ℕ) : (keyLB Y k).IsLB := by
  refine GlobalTheory.LBLimit.isLB_of_germs _ (GlobalTheory.FlagMod.exists_gChart hP) fun a b d y ha hb hd => ?_
  have e₁ : gm (𝟙 Y.X) y _ (thUnit a b) * gm (𝟙 Y.X) y _ (thUnit b d) = gm (𝟙 Y.X) y _ (thUnit a d) :=
    gm_cocycle (GlobalTheory.FlagMod.isLB_pushPP hP) (𝟙 Y.X) y ha hb hd
  have e₂ : gm (𝟙 Y.X) y _ (detChg a.toMChart b.toMChart) * gm (𝟙 Y.X) y _ (detChg b.toMChart d.toMChart) =
      gm (𝟙 Y.X) y _ (detChg a.toMChart d.toMChart) :=
    gm_cocycle (GlobalTheory.FlagMod.isLB_detLie hP) (𝟙 Y.X) y (i := a.toMChart) (j := b.toMChart) (k := d.toMChart) ha hb hd
  refine (congrArg₂ (· * ·) (gm_keyUnit k a b y) (gm_keyUnit k b d y)).trans (Eq.trans ?_ (gm_keyUnit k a d y).symm)
  rw [← e₁, ← e₂, mul_inv, mul_pow, mul_pow, _root_.mul_mul_mul_comm]

end Cover

def KeyAt (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn R) : Prop :=
  ∃ (φ : x.P.A.left ⟶ Y.t.G.left) (he : eSec x.P.A ≫ φ = z ≫ eSec Y.t.G)
    (w : LB.Iso x.P.L (Y.t.PP.L.pull φ)) (hg : x.P.g = M.n),
    IsGrpPullback x.P.A Y.t.G z φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ z he Y.t.PP.L Y.t.PP.rig) ∧
    (∀ (j : (Y.t.PP.L.pull φ).ι) (i : x.P.L.ι)
      (h : (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U (j PUnit.unit))),
      (φ.appLE _ _ h).hom (M.θ (j PUnit.unit)) =
        (show Γ(x.P.A.left, (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    ∀ i, (x.v i).left ≫ φ = spMap (dualMap (ev z M.U hz)) ≫ M.v₀ (i.cast hg)

end OneModel

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

@[reducible] def base : Model (S.Xo ct.Xm.i.l) ct.Xm.i.c (ct.Xm.i.c.V ct.W).subtype :=
  haveI := ct.B.iso none
  modelOfIso (ct.Y ct.Xm.i) ct.Xm.π (@GlobalTheory.IsNormalScheme.pred _ ct.Xm.normal) ct.Xm.t ct.Xm.tMap

theorem range_base_j : Set.range ct.base.j = ct.Xm.opn := by
  haveI := ct.B.iso none
  have e : ct.base.j ≫ ct.Xm.π = (ct.Y ct.Xm.i).j := modelOfIso_j _ _ _ _ _
  ext x
  rw [Pre.opn, ← e]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, Scheme.Hom.comp_apply _ _ _⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, ct.Xm.π.homeomorph.injective ((Scheme.Hom.comp_apply _ _ _).symm.trans hy)⟩

instance isNoetherianRing_base : IsNoetherianRing (ct.Xm.i.c.V ct.W) :=
  GlobalTheory.ModelPresentation.isNoetherianRing_place _ _ ct.hp.ne_zero ct.hW

theorem pushInvertible : PushInvertible ct.Xm.t.G ct.Xm.t.PP.L :=
  haveI := ct.B.iso none
  pushInvertible_modelOfIso (ct.Y ct.Xm.i) ct.Xm.π (@GlobalTheory.IsNormalScheme.pred _ ct.Xm.normal) ct.Xm.t ct.Xm.tMap
    ((GlobalTheory.CoeffRings.coeff_isDedFrac _ A.H _ ct.Xm.i.c).2.2.2 p ct.W ct.hp ct.hW).1
    ((S.sys.clauses p ct.W ct.hp ct.hW).1.1 ct.Xm.i).2.2.1

abbrev KeyChart : Type := GChart ct.base

def keyL (c : ℕ) : LB ct.Xm.X := keyLB ct.base c

theorem isLB_keyL (c : ℕ) : (ct.keyL c).IsLB := isLB_keyLB (Y := ct.base) ct.pushInvertible c

def ofModIso {Z : ct.Mdl} {F : Z.X.Modules} (h : GlobalTheory.VB.IsVB F 1) : (Z.ofMod F).toMod ≅ F :=
  haveI := h.isFiniteQC
  (GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso _ _ _ _ p ct.W ct.hp ct.hW _ _ Z F).some

def piPP : ct.Sh ct.Xm := ct.Xm.ofMod (pushMod ct.Xm.t)

def keySh (c : ℕ) : ct.Sh ct.Xm := ct.Xm.ofMod (toMod (ct.keyL c))

theorem isVB_pushMod : GlobalTheory.VB.IsVB (pushMod ct.Xm.t) 1 :=
  GlobalTheory.LocM.isVB_pushMod (Y := ct.base) (GlobalTheory.FlagMod.isLB_pushPP ct.pushInvertible)

def piIso : ct.piPP.toMod ≅ pushMod ct.Xm.t := ct.ofModIso ct.isVB_pushMod

def keyIso (c : ℕ) : (ct.keySh c).toMod ≅ toMod (ct.keyL c) := ct.ofModIso (GlobalTheory.VB.isVB_toMod (ct.isLB_keyL c))

theorem isInv_piPP : ct.IsInv ct.piPP := ct.isVB_pushMod.of_iso ct.piIso.symm

theorem isInv_keySh (c : ℕ) : ct.IsInv (ct.keySh c) :=
  (GlobalTheory.VB.isVB_toMod (ct.isLB_keyL c)).of_iso (ct.keyIso c).symm

variable {ct}

def keyGen (c : ℕ) (M : ct.KeyChart) : Γ((ct.keySh c).toMod, M.U) :=
  (ct.keyIso c).inv.app M.U (GlobalTheory.LB.chartSec (ct.isLB_keyL c) M)

theorem isFrame_keyGen (c : ℕ) (M : ct.KeyChart) : GlobalTheory.LB.IsFrame (keyGen c M) :=
  (GlobalTheory.LB.isFrame_chartSec (ct.isLB_keyL c) M).app (ct.keyIso c).symm

def keyCoef {c : ℕ} {V : ct.Xm.X.Opens} (s : Γ((ct.keySh c).toMod, V)) (M : ct.KeyChart) : Γ(ct.Xm.X, V ⊓ M.U) :=
  GlobalTheory.LB.coord ((ct.keyIso c).hom.app V s) M

def keyMk (c : ℕ) {V : ct.Xm.X.Opens} (f : ∀ M : ct.KeyChart, Γ(ct.Xm.X, V ⊓ M.U)) (hf : f ∈ secOn (ct.keyL c) V) :
    Γ((ct.keySh c).toMod, V) :=
  (GlobalTheory.LB.appLinearEquiv (ct.keyIso c) V).symm (GlobalTheory.LB.mkSec f hf)

theorem keyCoef_keyMk (c : ℕ) {V : ct.Xm.X.Opens} (f : ∀ M : ct.KeyChart, Γ(ct.Xm.X, V ⊓ M.U))
    (hf : f ∈ secOn (ct.keyL c) V) : keyCoef (keyMk c f hf) = f :=
  congrArg GlobalTheory.LB.coord ((GlobalTheory.LB.appLinearEquiv (ct.keyIso c) V).apply_symm_apply _)

def HasKeyValues {c : ℕ} (val : GlobalTheory.KeyCl.Rule) (s : ct.Sec (ct.keySh c)) : Prop :=
  ∀ (M : ct.KeyChart) (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ ct.Xm.X) (hz : ⊤ ≤ z ⁻¹ᵁ (ct.Xm.genO ⊓ M.U))
    (x : KeyIn K), KeyAt M z (GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz) x → ev z _ hz (keyCoef s M) = val K x

variable (ct)

open Classical in

def pbKF {g c : ℕ} (kf : KF g c) : ct.Sec (ct.keySh c) :=
  if h : ∃ s : ct.Sec (ct.keySh c), HasKeyValues kf.coef s then h.choose else 0

end At

def keyTrue (ct : At S κ p) : KeySt ct where
  piPP := ct.piPP
  keySh := ct.keySh
  keySh_inv _ := ct.isInv_keySh

example (ct : At S κ p) : ∃ s : Γ((ct.keySh 0).toMod, ⊤), ∀ M, At.keyCoef s M = 1 := by
  refine ⟨At.keyMk 0 (fun _ => 1) fun M M' => ?_, fun M => congrFun (At.keyCoef_keyMk _ _ _) M⟩
  change resG _ _ 1 = resG _ _ (keyUnit 0 M M').val * resG _ _ 1
  simp [keyUnit]

example (ct : At S κ p) (M M' : ct.KeyChart) :
    thRat M M' ^ 2 * (keyUnit 1 M M').val = GlobalTheory.FlagMod.rdet (GlobalTheory.FlagMod.chg M.toMChart M'.toMChart) := by
  simpa only [Nat.mul_one, pow_one, GlobalTheory.FlagMod.detChg_val] using thRat_pow_mul_keyUnit 1 M M'

example (ct : At S κ p) (c : ℕ) (M : ct.KeyChart) : At.keyGen c M ≠ 0 := fun h => by
  have := M.dom
  refine one_ne_zero ((At.isFrame_keyGen c M M.U le_rfl).1 ?_)
  simp only [h, map_zero, smul_zero]

end GlobalTheory.LocM
end
end
