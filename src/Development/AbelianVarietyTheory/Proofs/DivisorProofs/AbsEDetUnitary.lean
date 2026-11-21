import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactFundamentalSet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GramOfIsWittBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.WeilRangeOfAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOriginStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableRangeOneDetUnitElementary

section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.SWLit

namespace GlobalTheory.SiegelCoefTheta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n m : ℕ} {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]

def antiPt (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ) (x : κ → AF F) :
    Matrix (Fin m) (Fin (n + n)) (AE F E) :=
  co.e.symm (x, 0)

variable (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ)

variable {co}

end GlobalTheory.SiegelCoefTheta
end
end

section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.TowU GlobalTheory.SiegelCoefTheta

namespace GlobalTheory.WeilEx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Impl

variable {a b : ℕ} {JX : Matrix (Fin a) (Fin a) E} {JW : Matrix (Fin b) (Fin b) E} {κ : Type} [Fintype κ]

structure Impl (ψ : AddChar (AF F) ℂ) (co : Darboux (sy σ JX JW) κ) (g : UA σ JX × UA σ JW)
    (S : Module.End ℂ ((κ → AF F) → ℂ)) : Prop where
  pres : ∀ φ ∈ schA F κ, S φ ∈ schA F κ
  Heisenberg₂ : ∀ w, ∀ φ ∈ schA F κ, S (co.rho ψ w φ) = co.rho ψ (actAB (cA σ) g w) (S φ)
  adm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ S ∈ (adeleClass F).adm κ
  unit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

theorem actAB_mul (g g' : UA σ JX × UA σ JW) (w : Matrix (Fin a) (Fin b) (AE F E)) :
    actAB (cA σ) (g * g') w = actAB (cA σ) g (actAB (cA σ) g' w) := by
  simp only [actAB, Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]

variable {ψ : AddChar (AF F) ℂ} {co : Darboux (sy σ JX JW) κ}

theorem Impl.mul {g g' : UA σ JX × UA σ JW} {S S' : Module.End ℂ ((κ → AF F) → ℂ)} (h : Impl ψ co g S)
    (h' : Impl ψ co g' S') : Impl ψ co (g * g') (S * S') :=
  ⟨fun φ hφ => h.pres _ (h'.pres φ hφ),
    fun w φ hφ => by
      rw [Module.End.mul_apply, h'.Heisenberg₂ w φ hφ, h.Heisenberg₂ _ _ (h'.pres φ hφ), actAB_mul, Module.End.mul_apply],
    fun l hl => h'.adm _ (h.adm l hl),
    fun μ hμ φ hφ => by rw [Module.End.mul_apply, h.unit μ hμ _ (h'.pres φ hφ), h'.unit μ hμ φ hφ]⟩

end Impl

variable {n m : ℕ} {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]

variable (σ JV J₂) in

def parG : Subgroup (UA σ JV × UA σ J₂) :=
  (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype).comap (MonoidHom.snd _ _)

def toP : parG σ JV J₂ →* siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype :=
  ((MonoidHom.snd (UA σ JV) (UA σ J₂)).comp (parG σ JV J₂).subtype).codRestrict _ fun q => q.2

def detP : parG σ JV J₂ →* (AE F E)ˣ :=
  (aOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype).comp toP

def scal (χ : Chr F E) (q : parG σ JV J₂) : ℂ :=
  (χ (detP q) : ℂ) * Doubling.npow (absE F E (detP q)) ((m : ℂ) / 2)

def parOp (ψ : AddChar (AF F) ℂ) (χ : Chr F E) (co : Darboux (sy σ JV J₂) κ) (q : parG σ JV J₂) :
    Module.End ℂ ((κ → AF F) → ℂ) where
  toFun Φ x := scal χ q * co.rho ψ (actAB (cA σ) (q.1)⁻¹ (antiPt co x)) Φ 0
  map_add' Φ Φ' := by funext x; simp only [Darboux.rho, schr, Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

variable (E) in

def diagA (d : Fin n → AF F) : Matrix (Fin n) (Fin n) (AE F E) :=
  Matrix.diagonal fun j => algebraMap (AF F) (AE F E) (d j)

open scoped Classical in
variable (F) in

def nInf : AF F →* ℝ where
  toFun a := ∏ w : {w : InfinitePlace F // w.IsReal}, (evI F a).1 w
  map_one' := by
    rw [show evI F 1 = 1 from map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)]
    simp
  map_mul' a b := by
    rw [show evI F (a * b) = evI F a * evI F b from map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1]
    simp [Finset.prod_mul_distrib]

section Gauss

variable {ι : Type} [Fintype ι]

def gaussB (α : ι → F) (D : F) (x y : ι ⊕ ι → AF F) : AF F :=
  2 * ∑ k, algebraMap F (AF F) (α k) *
    (x (.inl k) * y (.inl k) + algebraMap F (AF F) D * (x (.inr k) * y (.inr k)))

end Gauss

end GlobalTheory.WeilEx

end
end

section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.TowU GlobalTheory.SiegelCoefTheta
open GlobalTheory.WeilEx
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.WeilEx.Jac

section Alg

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] {α β ν X : Type} [Fintype β] [DecidableEq β]
  [AddCommGroup X] [Module R X] {e : ν ⊕ ν ≃ α}

omit [DecidableEq β] in

def lmul [Fintype α] [DecidableEq α] (β : Type) (t : GL α A) : Matrix α β A ≃ₗ[R] Matrix α β A where
  toFun w := (t : Matrix α α A) * w
  invFun w := ((t⁻¹ : GL α A) : Matrix α α A) * w
  map_add' _ _ := Matrix.mul_add _ _ _
  map_smul' c w := by
    simp only [RingHom.id_apply]
    exact Matrix.mul_smul _ c w
  left_inv w := by
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  right_inv w := by
    simp only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

variable [Invertible (2 : R)] {D : Matrix α β A ≃ₗ[R] X × X} (hΔ : ∀ w, LinAct.Del e w → (D w).1 = 0)
  (hN : ∀ w, LinAct.Nab e w → (D w).2 = 0)
include hΔ hN

end Alg

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem absE_det_unitary {k : ℕ} {J : Matrix (Fin k) (Fin k) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    absE F E (Matrix.GeneralLinearGroup.det (g : GL (Fin k) (AE F E))) = 1 := by
  set d := Matrix.GeneralLinearGroup.det (g : GL (Fin k) (AE F E)) with hd
  have hJu : IsUnit (incM F J).det := by
    have e0 : (incM F J).det = inclR (F := F) (AF F) J.det := (RingHom.map_det _ _).symm
    rw [e0]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  have h := congrArg Matrix.det (show ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E))ᵀ * incM F J *
    ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).map (cA σ) = incM F J from g.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).map (cA σ)).det =
      cA σ ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).det from
      ((cA σ).toRingHom.map_det _).symm] at h
  have h2 : (d : AE F E) * cA σ d = 1 := by
    rw [hd, Matrix.GeneralLinearGroup.val_det_apply]
    exact hJu.mul_left_cancel (by linear_combination h)
  have hc : Units.map (cA σ : AE F E →* AE F E) d = conjUnit σ d := by
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rfl
  have h3 : d * Units.map (cA σ : AE F E →* AE F E) d = 1 := Units.ext (by simpa using h2)
  have h4 : absE F E d * absE F E d = 1 := by
    nth_rewrite 2 [← absE_conjUnit σ d]
    rw [← hc, ← map_mul, h3, map_one]
  apply NNReal.coe_injective
  have h6 : (absE F E d : ℝ) * absE F E d = 1 := by exact_mod_cast h4
  have h7 : (0 : ℝ) ≤ absE F E d := (absE F E d).2
  push_cast
  exact le_antisymm (by nlinarith) (by nlinarith)

end Main

end GlobalTheory.WeilEx.Jac
end
end
