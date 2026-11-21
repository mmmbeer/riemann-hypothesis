import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomTw
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionElement
import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotInv

section
set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open NumberField Formalism.BasicNotions Formalism.MainNotions.S.Lat Module
open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Bridge
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable (D : D7) (large₂ : SizeData₂ D)

def MomNorm' (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    ∀ (A : LocS W) (hA : GoodS D lam' A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'),
    ∃ (Bf : A.H → W.Wp) (P : Mx D.R.k D.R.rS) (w0 : A.H),
      IsBesselMapSm W.z (psi D.R.k D.R.rS W.z (cOfDpsi ((kaS D : ℝ) : ℂ))) A.σ W.π Bf ∧
      (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ,
        l2SG W.νS (fun g => Bf (A.σ g v)) = (‖v‖₊ : ℝ≥0∞) ^ 2) ∧
      IsCayleyU D.R.k D.R.rS (epsSH D.R) P ∧
      w0 ∈ shell (toBesselK D τ w w' θ W lam' A hW hA hT hT') P 0 ∧ w0 ≠ 0 ∧
      ∀ F : (Fin (D.R.rS + 1) → ℝ) → ℝ≥0∞, Measurable F →
        ∫⁻ x, F (fun a => lA D.R.k D.R.rS W.z (Matrix.of x) a) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
          l2SG W.νS A.Φ * Emom (toBesselK D τ w w' θ W lam' A hW hA hT hT') Bf W.νS w0
            (fun g => F (fun a => lA D.R.k D.R.rS W.z g a))

end

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 C1 : ℝ)

def MomF' : Prop :=
  ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => MomNorm' (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn

end Fam

section
variable (D : D7) (large₂ : SizeData₂ D)

def BesselSchur' (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → ∀ (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ (A : LocS W), GoodS D lam' A → 0 < Tr D w →
    ∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ,
      l2SG W.νS (fun g => A.B (A.σ g v)) * (‖A.v0‖₊ : ℝ≥0∞) ^ 2 = l2SG W.νS A.Φ * (‖v‖₊ : ℝ≥0∞) ^ 2

end

end Formalism.MainNotions.S.Pv.Mom
end
end

section
open Matrix

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]

theorem twT_mul_block_mul {h m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : WeylGroupFacts.block k r h) :
    twT k r * (h * m) = h * (twT k r * m * twTi k r) * twT k r := by
  rw [← Matrix.mul_assoc, twT_comm_block hh]
  simp only [Matrix.mul_assoc, twTi_mul_twT, Matrix.mul_one]

theorem bessel_twist (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (hone : σ 1 = 1)
    (hmul : ∀ x ∈ UH (Hpk k r), ∀ y ∈ UH (Hpk k r), σ (x * y) = (σ x).comp (σ y))
    (hiso : ∀ x ∈ UH (Hpk k r), ∀ v, ‖σ x v‖ = ‖v‖)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {c : ℂ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hB : IsBesselMapSm z (psi k r z c) σ π B) :
    IsBesselMapSm z (psi k r z (c * -Complex.I)) σ π (fun v => B (σ (twT k r) v)) := by
  have hsm : ∀ v ∈ smoothVecs (k := k) (r := r) σ, σ (twT k r) v ∈ smoothVecs (k := k) (r := r) σ :=
    fun v hv => smooth_vectors_translate σ hmul twT_mem_UH hv
  refine ⟨fun v hv w hw => ?_, fun a v hv => ?_, fun h hh m hm v hv => ?_, ?_⟩
  · show B (σ (twT k r) (v + w)) = B (σ (twT k r) v) + B (σ (twT k r) w)
    rw [map_add]; exact hB.1 _ (hsm v hv) _ (hsm w hw)
  · show B (σ (twT k r) (a • v)) = a • B (σ (twT k r) v)
    rw [map_smul]; exact hB.2.1 a _ (hsm v hv)
  · show B (σ (twT k r) (σ (h * m) v)) = psi k r z (c * -Complex.I) m • π h (B (σ (twT k r) v))
    have hhU : h ∈ UH (Hpk k r) := hh.1
    have hmU : m ∈ UH (Hpk k r) := hm.1
    have hm' := twT_conj_N hm
    have e1 : σ (twT k r) (σ (h * m) v) = σ (h * (twT k r * m * twTi k r)) (σ (twT k r) v) := by
      have a1 : σ (twT k r) (σ (h * m) v) = σ (twT k r * (h * m)) v := by
        rw [hmul _ twT_mem_UH _ (WeylGroupFacts.uh_mul hhU hmU)]; rfl
      have a2 : σ (h * (twT k r * m * twTi k r)) (σ (twT k r) v) =
          σ (h * (twT k r * m * twTi k r) * twT k r) v := by
        rw [hmul _ (WeylGroupFacts.uh_mul hhU hm'.1) _ twT_mem_UH]; rfl
      rw [a1, a2, twT_mul_block_mul (WeylGroupFacts.uw_block hh)]
    rw [e1, hB.2.2.1 h hh _ hm' _ (hsm v hv), twT_psi hz]
  · obtain ⟨C, Ws, hWs, hbd⟩ := hB.2.2.2
    refine ⟨C, Ws.map (List.map fun X => twTi k r * X * twT k r), ?_, fun v hv => ?_⟩
    · intro w hw X hX
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
      obtain ⟨X0, hX0, rfl⟩ := List.mem_map.1 hX
      exact lie_algebra_conj_mem twTi_mem_UH twT_mem_UH twTi_mul_twT (hWs w0 hw0 X0 hX0)
    · have h1 := hbd _ (hsm v hv)
      have e : ∀ w ∈ Ws, ‖dsigW (k := k) (r := r) σ w (σ (twT k r) v)‖ =
          ‖dsigW (k := k) (r := r) σ (w.map fun X => twTi k r * X * twT k r) v‖ := by
        intro w hw
        rw [derivative_word_translate σ hmul hone twTi_mem_UH twT_mem_UH twTi_mul_twT w (hWs w hw) v, hiso _ twT_mem_UH]
      rw [List.map_map]
      calc ‖B (σ (twT k r) v)‖ ≤ C * (Ws.map fun w => ‖dsigW (k := k) (r := r) σ w (σ (twT k r) v)‖).sum := h1
        _ = C * (Ws.map ((fun w => ‖dsigW (k := k) (r := r) σ w v‖) ∘ List.map fun X => twTi k r * X * twT k r)).sum := by
          congr 2
          exact List.map_congr_left e

end Formalism.MainNotions.S.Pv.Mom
end
end

section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.FrameBoundFromBesselTorus

variable {k r : ℕ}

def cjX (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  twT k r * X * twTi k r

def cjM (x : Mt k r) : Mt k r := fun i j => (twT k r * Matrix.of x * twTi k r) i j

theorem isUnit_twT : IsUnit (twT k r) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse twT_mul_twTi)

theorem exp_cjX (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    NormedSpace.exp (cjX X) = cjX (NormedSpace.exp X) := by
  unfold cjX
  rw [← twT_inv]
  exact Matrix.exp_conj _ _ isUnit_twT

theorem cjX_smul (c : ℂ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : cjX (c • X) = c • cjX (k := k) (r := r) X := by
  unfold cjX; rw [Matrix.mul_smul, Matrix.smul_mul]

theorem cjX_add (X Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : cjX (X + Y) = cjX (k := k) (r := r) X + cjX Y := by
  unfold cjX; rw [Matrix.mul_add, Matrix.add_mul]

theorem cjX_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    cjX X i j = twD k r i * X i j * star (twD k r j) := twT_conj_apply X i j

theorem cjX_mem_lieOf {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hX : X ∈ lieOf (Nset k r)) :
    cjX X ∈ lieOf (Nset k r) := by
  intro t
  rw [← cjX_smul, exp_cjX]
  exact twT_conj_N (hX t)

def cjXI (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  twTi k r * X * twT k r

theorem cjX_cjXI (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : cjX (cjXI (k := k) (r := r) X) = X := by
  unfold cjX cjXI
  simp only [← Matrix.mul_assoc, twT_mul_twTi, Matrix.one_mul]
  rw [Matrix.mul_assoc, twT_mul_twTi, Matrix.mul_one]

theorem cjXI_cjX (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : cjXI (cjX (k := k) (r := r) X) = X := by
  unfold cjX cjXI
  simp only [← Matrix.mul_assoc, twTi_mul_twT, Matrix.one_mul]
  rw [Matrix.mul_assoc, twTi_mul_twT, Matrix.mul_one]

theorem twTi_conj_N {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) :
    twTi k r * n * twT k r ∈ Nset k r := by
  rw [WeylGroupFacts.nset_iff] at hn ⊢
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul twTi_mem_UH hn.1) twT_mem_UH, fun i j hj hi => ?_⟩
  have e : (twTi k r * n * twT k r) i j = star (twD k r i) * n i j * twD k r j := by
    unfold twT twTi; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [e, hn.2 i j hj hi]
  split_ifs with h
  · subst h; rw [mul_one, star_twD_mul]
  · simp

theorem exp_cjXI (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    NormedSpace.exp (cjXI X) = cjXI (k := k) (r := r) (NormedSpace.exp X) := by
  unfold cjXI
  rw [← twTi_inv]
  exact Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse twTi_mul_twT))

theorem cjXI_mem_lieOf {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hX : X ∈ lieOf (Nset k r)) :
    cjXI X ∈ lieOf (Nset k r) := by
  intro t
  have e : cjXI (k := k) (r := r) ((t : ℂ) • X) = (t : ℂ) • cjXI X := by
    unfold cjXI; rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← e, exp_cjXI]
  exact twTi_conj_N (hX t)

theorem realifyFun_add (X Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    realifyFun (X + Y) = realifyFun X + realifyFun Y := by
  funext p; rcases p with ⟨i, j, b⟩; cases b <;> simp [realifyFun]

theorem realifyFun_smul (c : ℝ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    realifyFun ((c : ℂ) • X) = c • realifyFun X := by
  funext p; rcases p with ⟨i, j, b⟩; cases b <;> simp [realifyFun]

def rotE (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hadd : ∀ X Y, f (X + Y) = f X + f Y) (hsm : ∀ (c : ℂ) X, f (c • X) = c • f X) :
    EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) where
  toFun y := WithLp.toLp 2 (realifyFun (f (unrealify y)))
  map_add' x y := by
    rw [unrealify_add', hadd, realifyFun_add]; rfl
  map_smul' c x := by
    rw [unrealify_smul', hsm, realifyFun_smul]; rfl

theorem unrealify_toLp (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    unrealify (WithLp.toLp 2 (realifyFun X) : EuclideanSpace ℝ (IxE k r)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

theorem realify_unrealify (y : EuclideanSpace ℝ (IxE k r)) :
    (WithLp.toLp 2 (realifyFun (unrealify y)) : EuclideanSpace ℝ (IxE k r)) = y := by
  ext ⟨i, j, b⟩
  cases b <;> simp [unrealify, realifyFun]

theorem sumSq_realify (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ∑ p : IxE k r, (realifyFun X p) ^ 2 = ∑ i, ∑ j, Complex.normSq (X i j) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp [realifyFun, Complex.normSq_apply]
  ring

theorem norm_sq_toLp (f : IxE k r → ℝ) : ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (IxE k r))‖ ^ 2 = ∑ p, f p ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp

theorem normSq_cjX (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    Complex.normSq (cjX X i j) = Complex.normSq (X i j) := by
  rw [cjX_apply, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_eq_norm_sq (twD k r i),
    Complex.normSq_eq_norm_sq (star (twD k r j)), norm_star, norm_twD, norm_twD]
  ring

def rotC (k r : ℕ) : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) :=
  rotE (k := k) (r := r) cjX cjX_add cjX_smul

def rotCI (k r : ℕ) : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) :=
  rotE (k := k) (r := r) cjXI
    (fun X Y => by unfold cjXI; rw [Matrix.mul_add, Matrix.add_mul])
    (fun c X => by unfold cjXI; rw [Matrix.mul_smul, Matrix.smul_mul])

theorem rotC_apply (y : EuclideanSpace ℝ (IxE k r)) : rotC k r y = WithLp.toLp 2 (realifyFun (cjX (unrealify y))) := rfl

theorem rotCI_apply (y : EuclideanSpace ℝ (IxE k r)) :
    rotCI k r y = WithLp.toLp 2 (realifyFun (cjXI (unrealify y))) := rfl

theorem rotC_rotCI (y : EuclideanSpace ℝ (IxE k r)) : rotC k r (rotCI k r y) = y := by
  rw [rotC_apply, rotCI_apply, unrealify_toLp, cjX_cjXI, realify_unrealify]

theorem rotCI_rotC (y : EuclideanSpace ℝ (IxE k r)) : rotCI k r (rotC k r y) = y := by
  rw [rotC_apply, rotCI_apply, unrealify_toLp, cjXI_cjX, realify_unrealify]

theorem norm_rotC (y : EuclideanSpace ℝ (IxE k r)) : ‖rotC k r y‖ = ‖y‖ := by
  have h1 : ‖rotC k r y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [rotC_apply, norm_sq_toLp, sumSq_realify]
    conv_rhs => rw [← realify_unrealify y, norm_sq_toLp, sumSq_realify]
    simp only [normSq_cjX]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

theorem rotC_mem : ∀ x ∈ lieE (Nset k r), rotC k r x ∈ lieE (Nset k r) := by
  intro x hx
  refine span_mem_of_image ?_ hx
  rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  refine ⟨cjX X, cjX_mem_lieOf hX, ?_⟩
  show _ = rotC k r ((WithLp.equiv 2 _).symm (realifyFun X))
  rw [rotC_apply]
  congr 2

theorem rotCI_mem : ∀ x ∈ lieE (Nset k r), rotCI k r x ∈ lieE (Nset k r) := by
  intro x hx
  refine span_mem_of_image ?_ hx
  rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  refine ⟨cjXI X, cjXI_mem_lieOf hX, ?_⟩
  show _ = rotCI k r ((WithLp.equiv 2 _).symm (realifyFun X))
  rw [rotCI_apply]
  congr 2

def rotLE (k r : ℕ) : lieE (Nset k r) ≃ₗ[ℝ] lieE (Nset k r) :=
  LinearEquiv.ofLinear ((rotC k r).restrict rotC_mem) ((rotCI k r).restrict rotCI_mem)
    (LinearMap.ext fun x => by apply Subtype.ext; exact rotC_rotCI _)
    (LinearMap.ext fun x => by apply Subtype.ext; exact rotCI_rotC _)

def rotIso (k r : ℕ) : lieE (Nset k r) ≃ₗᵢ[ℝ] lieE (Nset k r) :=
  { rotLE k r with norm_map' := fun x => norm_rotC (k := k) (r := r) x.1 }

theorem measurable_cjM : Measurable (cjM (k := k) (r := r)) := by
  have : Continuous (cjM (k := k) (r := r)) := by
    have h : Continuous (fun x : Mt k r => (twT k r * Matrix.of x * twTi k r : Matrix _ _ ℂ)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact h
  exact this.measurable

theorem cjM_expL (x : lieE (Nset k r)) : cjM (expL (Nset k r) x) = expL (Nset k r) (rotIso k r x) := by
  funext i j
  show cjX (NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (IxE k r)))) i j =
    NormedSpace.exp (unrealify ((rotC k r) (x : EuclideanSpace ℝ (IxE k r)))) i j
  rw [rotC_apply, unrealify_toLp, exp_cjX]

theorem map_haarLie_cjM (κN : ENNReal) : (haarLie (Nset k r) κN).map cjM = haarLie (Nset k r) κN := by
  have e : cjM ∘ expL (Nset k r) = expL (Nset k r) ∘ (rotIso k r) := funext cjM_expL
  have h0 : haarLie (Nset k r) κN = κN • (volume : Measure (lieE (Nset k r))).map (expL (Nset k r)) := rfl
  rw [h0, Measure.map_smul, Measure.map_map measurable_cjM (continuous_expL _).measurable, e,
    ← Measure.map_map (continuous_expL _).measurable (rotIso k r).continuous.measurable,
    (rotIso k r).measurePreserving.map_eq]

theorem twTi_comm_block {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : WeylGroupFacts.block k r h) :
    twTi k r * h = h * twTi k r := by
  have e := twT_comm_block hh
  calc twTi k r * h = twTi k r * h * (twT k r * twTi k r) := by rw [twT_mul_twTi, Matrix.mul_one]
    _ = twTi k r * (h * twT k r) * twTi k r := by simp only [Matrix.mul_assoc]
    _ = twTi k r * (twT k r * h) * twTi k r := by rw [e]
    _ = h * twTi k r := by rw [← Matrix.mul_assoc, twTi_mul_twT, Matrix.one_mul]

theorem twT_conj_S {z : Fin (2 * r + k + 1) → ℂ} {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ Sset k r z) :
    twT k r * s * (twT k r)⁻¹ ∈ Sset k r z ∧ (twT k r)⁻¹ * s * twT k r ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hb := WeylGroupFacts.uw_block hh
  rw [twT_inv]
  constructor
  · refine ⟨h, hh, twT k r * m * twTi k r, twT_conj_N hm, ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, twT_comm_block hb]; simp only [Matrix.mul_assoc]
  · refine ⟨h, hh, twTi k r * m * twT k r, twTi_conj_N hm, ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, twTi_comm_block hb]; simp only [Matrix.mul_assoc]

theorem map_muS_cjM {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)} (κN : ENNReal)
    (hW : IsHaarOn (UWset k r z) μW) :
    (muS μW (haarLie (Nset k r) κN)).map (fun x => fun i j => (twT k r * Matrix.of x * (twT k r)⁻¹) i j) =
      muS μW (haarLie (Nset k r) κN) := by
  rw [twT_inv]
  have : SigmaFinite μW := hW.1
  have hsf : SFinite (haarLie (Nset k r) κN) := sFinite_haarLie _ _
  have hmul : Measurable (Formalism.MainNotions.BridgeCSB.mulP (k := k) (r := r)) := Formalism.MainNotions.BridgeCSB.continuous_mulP.measurable
  show ((μW.prod (haarLie (Nset k r) κN)).map Formalism.MainNotions.BridgeCSB.mulP).map cjM =
    (μW.prod (haarLie (Nset k r) κN)).map Formalism.MainNotions.BridgeCSB.mulP
  rw [Measure.map_map measurable_cjM hmul]
  have hae : cjM ∘ Formalism.MainNotions.BridgeCSB.mulP =ᵐ[μW.prod (haarLie (Nset k r) κN)]
      Formalism.MainNotions.BridgeCSB.mulP ∘ Prod.map id cjM := by
    have h0 : (μW.prod (haarLie (Nset k r) κN)) ({x | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ) = 0 := by
      rw [Measure.prod_prod, hW.2.2.1, zero_mul]
    refine Filter.eventuallyEq_of_mem (s := ({x | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ)ᶜ)
      (measure_eq_zero_iff_ae_notMem.mp h0 |> fun h => by
        rw [Filter.Eventually] at h; simpa [Set.compl_def] using h) ?_
    intro p hp
    have hp1 : Matrix.of p.1 ∈ UWset k r z := by
      by_contra hc
      exact hp ⟨hc, Set.mem_univ _⟩
    have hb := WeylGroupFacts.uw_block hp1
    funext i j
    show (twT k r * Matrix.of (Formalism.MainNotions.BridgeCSB.mulP p) * twTi k r) i j =
      (Matrix.of p.1 * Matrix.of (cjM p.2)) i j
    have e1 : (Matrix.of (Formalism.MainNotions.BridgeCSB.mulP p) : Matrix _ _ ℂ) = Matrix.of p.1 * Matrix.of p.2 := rfl
    have e2 : (Matrix.of (cjM p.2) : Matrix _ _ ℂ) = twT k r * Matrix.of p.2 * twTi k r := rfl
    rw [e1, e2, ← Matrix.mul_assoc, twT_comm_block hb]
    simp only [Matrix.mul_assoc]
  rw [Measure.map_congr hae, ← Measure.map_map hmul (measurable_id.prodMap measurable_cjM)]
  have hmp : MeasurePreserving (Prod.map id cjM) (μW.prod (haarLie (Nset k r) κN)) (μW.prod (haarLie (Nset k r) κN)) :=
    (MeasurePreserving.id μW).prod ⟨measurable_cjM, map_haarLie_cjM κN⟩
  rw [hmp.map_eq]

end Formalism.MainNotions.S.Pv.Mom
end
end

section
open MeasureTheory Matrix
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.QuotUniq

open Formalism.QuantumDeterminants Formalism.MainNotions.S

def QuotLeftNorm : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μG μS ν : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    IsHaarOn (UH (Hpk k r)) μG → IsHaarOn (Sset k r z) μS → IsQuotMeas μG μS ν →
    ∀ t ∈ UH (Hpk k r), (∀ s ∈ Sset k r z, t * s * t⁻¹ ∈ Sset k r z ∧ t⁻¹ * s * t ∈ Sset k r z) →
      μS.map (fun x => fun i j => (t * Matrix.of x * t⁻¹) i j) = μS →
      ∀ F : Mt k r → ENNReal, Measurable F →
        (∀ s ∈ Sset k r z, ∀ x : Mt k r, Matrix.of x ∈ UH (Hpk k r) → F (fun i j => (s * Matrix.of x) i j) = F x) →
        ∫⁻ x, F (fun i j => (t * Matrix.of x) i j) ∂ν = ∫⁻ x, F x ∂ν

section General

open PI PI.QuotInvW

variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)} {μG μS ν ν' : Measure (MtM m)}

theorem lintegral_eq_weight (h : QuotientSetting G S μG μS ν) {ρ : MtM m → ℝ≥0∞} (hρm : Measurable ρ)
    (hρ0 : ∀ x, ρ x ≠ 0) (hρi : ∫⁻ x, ρ x ∂μG ≠ ⊤) {F : MtM m → ℝ≥0∞} (hF : Measurable F)
    (hFi : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x) :
    ∫⁻ x, F x ∂ν = ∫⁻ x, F x * (avgS μS ρ x)⁻¹ * ρ x ∂μG := by
  have : SigmaFinite μS := h.2.2.2.2.1.1
  have hcm : Measurable (avgS μS ρ) := measurable_avgS hρm
  have hH : Measurable (fun x => F x * (avgS μS ρ x)⁻¹) := hF.mul hcm.inv
  have hHi : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G →
      F (mm s x) * (avgS μS ρ (mm s x))⁻¹ = F x * (avgS μS ρ x)⁻¹ := by
    intro s hs x hx
    rw [hFi s hs x hx, avgS_mm h hρm (t := s) hs x]
  have hw := weil_inv h hH hρm hHi
  have hint : ∫⁻ x, avgS μS ρ x ∂ν ≠ ⊤ := by
    have := weil h hρm
    rw [this] at hρi
    exact hρi
  have hfin : ∀ᵐ x ∂ν, avgS μS ρ x < ⊤ := ae_lt_top hcm hint
  rw [hw]
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with x hx
  change F x = F x * (avgS μS ρ x)⁻¹ * avgS μS ρ x
  rw [mul_assoc, ENNReal.inv_mul_cancel (avgS_ne_zero h hρm hρ0 x) hx.ne, mul_one]

theorem lintegral_eq_of_quot (h : QuotientSetting G S μG μS ν) (h' : QuotientSetting G S μG μS ν')
    {F : MtM m → ℝ≥0∞} (hF : Measurable F)
    (hFi : ∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (mm s x) = F x) :
    ∫⁻ x, F x ∂ν = ∫⁻ x, F x ∂ν' := by
  have : SigmaFinite μG := h.2.2.2.1.1
  obtain ⟨w, hw0, hwm, hwi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hρm : Measurable (fun x => (w x : ℝ≥0∞)) := hwm.coe_nnreal_ennreal
  have hρ0 : ∀ x, (w x : ℝ≥0∞) ≠ 0 := fun x => by simp [(hw0 x).ne']
  have hρi : ∫⁻ x, (w x : ℝ≥0∞) ∂μG ≠ ⊤ := (hwi.trans ENNReal.one_lt_top).ne
  rw [lintegral_eq_weight h hρm hρ0 hρi hF hFi, lintegral_eq_weight h' hρm hρ0 hρi hF hFi]

theorem isQuotM_map_left (h : QuotientSetting G S μG μS ν) {t : Matrix (Fin m) (Fin m) ℂ} (ht : t ∈ G)
    (hμ : μS.map (fun x : MtM m => fun i j => (t * Matrix.of x * t⁻¹) i j) = μS) :
    IsQuotM μG μS (ν.map (fun x : MtM m => fun i j => (t * Matrix.of x) i j)) := by
  intro f hf
  have : SigmaFinite μS := h.2.2.2.2.1.1
  set L : MtM m → MtM m := fun x => fun i j => (t * Matrix.of x) i j with hLdef
  set C : MtM m → MtM m := fun x => fun i j => (t * Matrix.of x * t⁻¹) i j with hCdef
  have hL : Measurable L := measurable_mm_right (m := m) t
  have hC : Measurable C :=
    (measurable_mm_left (m := m) (t⁻¹ : Matrix (Fin m) (Fin m) ℂ)).comp (measurable_mm_right (m := m) t)
  have hG' : μG.map L = μG := h.2.2.2.1.2.2.2 t ht
  have hinv : t⁻¹ * t = 1 := inv_mul_of h.1 ht
  have hA : Measurable (fun y : MtM m => ∫⁻ s, f (mm s y) ∂μS) := measurable_avgS hf
  have key : ∀ s x : MtM m, L (mm s x) = mm (C s) (L x) := by
    intro s x
    have e : t * Matrix.of s * t⁻¹ * (t * Matrix.of x) = t * (Matrix.of s * Matrix.of x) := by
      rw [Matrix.mul_assoc (t * Matrix.of s) t⁻¹, ← Matrix.mul_assoc t⁻¹ t, hinv, Matrix.one_mul,
        Matrix.mul_assoc]
    funext i j
    change (t * (Matrix.of s * Matrix.of x)) i j = (t * Matrix.of s * t⁻¹ * (t * Matrix.of x)) i j
    rw [e]
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, f x ∂(μG.map L) := by rw [hG']
    _ = ∫⁻ x, f (L x) ∂μG := lintegral_map hf hL
    _ = ∫⁻ x, (∫⁻ s, f (L (mm s x)) ∂μS) ∂ν := weil h (hf.comp hL)
    _ = ∫⁻ x, (∫⁻ s, f (mm s (L x)) ∂μS) ∂ν := by
        refine lintegral_congr fun x => ?_
        calc ∫⁻ s, f (L (mm s x)) ∂μS = ∫⁻ s, f (mm (C s) (L x)) ∂μS := by
              refine lintegral_congr fun s => ?_
              rw [key s x]
          _ = ∫⁻ s, f (mm s (L x)) ∂(μS.map C) :=
              (lintegral_map (hf.comp (measurable_mm_left (L x))) hC).symm
          _ = ∫⁻ s, f (mm s (L x)) ∂μS := by rw [hμ]
    _ = ∫⁻ y, (∫⁻ s, f (mm s y) ∂μS) ∂(ν.map L) := (lintegral_map hA hL).symm

end General

theorem quotLeftNorm : QuotLeftNorm := by
  intro k r z μG μS ν hz hT hG hS hq t ht hN hμS F hF hFS
  obtain ⟨h1, h2, h3, h4, h5⟩ := quotient_measure_unitary_group k r z hz hT
  have hset : PI.QuotientSetting (UH (Hpk k r)) (Sset k r z) μG μS ν :=
    ⟨h1, h2, h3, hG, hS, h4 μG hG, h5 μS hS, hq⟩
  have hq1 := isQuotM_map_left hset ht hμS
  have hL : Measurable (fun x : Mt k r => (fun i j => (t * Matrix.of x) i j : Mt k r)) :=
    PI.QuotInvW.measurable_mm_right (m := 2 * r + k + 1) t
  have e := lintegral_eq_of_quot ⟨h1, h2, h3, hG, hS, h4 μG hG, h5 μS hS, hq1⟩ hset hF
    (fun s hs x hx => hFS s hs x hx)
  rw [lintegral_map hF hL] at e
  exact e

end Formalism.MainNotions.S.Pv.QuotUniq

end
end

section
open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.LowestKTypeMultiplicity

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem bessel_smul {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hB : IsBesselMapSm z ψ σ π B) (α : ℂ) : IsBesselMapSm z ψ σ π (fun v => α • B v) := by
  obtain ⟨h1, h2, h3, C, Ws, hWs, hbd⟩ := hB
  refine ⟨fun v hv w hw => ?_, fun a v hv => ?_, fun h hh m hm v hv => ?_, ‖α‖ * C, Ws, hWs, fun v hv => ?_⟩
  · show α • B (v + w) = α • B v + α • B w
    rw [h1 v hv w hw, smul_add]
  · show α • B (a • v) = a • (α • B v)
    rw [h2 a v hv, smul_comm]
  · show α • B (σ (h * m) v) = ψ m • π h (α • B v)
    rw [h3 h hh m hm v hv, map_smul, smul_comm]
  · show ‖α • B v‖ ≤ ‖α‖ * C * _
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd v hv) (norm_nonneg _)

theorem twist_lintegral (hLN : Formalism.MainNotions.S.Pv.QuotUniq.QuotLeftNorm)
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UH (Hpk k r)) σ)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (c : ℂ)
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)}
    (hπ : ∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) {B : H → Wp} (hB : IsBesselMapSm z (psi k r z c) σ π B)
    {μG μW ν : Measure (Mt k r)} (κN : ℝ≥0∞) (hG : IsHaarOn (UH (Hpk k r)) μG) (hW : IsHaarOn (UWset k r z) μW)
    (hS : IsHaarOn (Sset k r z) (muS μW (haarLie (Nset k r) κN)))
    (hq : IsQuotMeas μG (muS μW (haarLie (Nset k r) κN)) ν) {u : H} (hu : IsSmoothVec (k := k) (r := r) σ u)
    {Φ0 : (Fin (r + 1) → ℝ) → ℝ≥0∞} (hΦ0 : Measurable Φ0) :
    ∫⁻ x, Φ0 (fun a => lA k r z (Matrix.of x) a) * (‖B (σ (twT k r) (σ (Matrix.of x) u))‖₊ : ℝ≥0∞) ^ 2 ∂ν =
      ∫⁻ x, Φ0 (fun a => lA k r z (Matrix.of x) a) * (‖B (σ (Matrix.of x) u)‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  have hconc := Formalism.MainNotions.BesselShellMomentBounds.quot_conc z μG _ ν hG hS hq
  have hae : ∀ᵐ x ∂ν, Matrix.of x ∈ UH (Hpk k r) := by rw [ae_iff]; exact hconc
  have hFm := Fu_meas hσ hB hu hΦ0
  have hmap := map_muS_cjM (z := z) κN hW
  have key : ∫⁻ x, Fu σ z B Φ0 u (fun i j => (twT k r * Matrix.of x) i j) ∂ν = ∫⁻ x, Fu σ z B Φ0 u x ∂ν :=
    hLN k r z μG (muS μW (haarLie (Nset k r) κN)) ν hz hT hG hS hq (twT k r) twT_mem_UH
      (fun s hs => twT_conj_S hs) hmap (Fu σ z B Φ0 u) hFm (Fu_leftS laLeftS_proved hσ hz c hπ hB Φ0 hu)
  have E1 : ∫⁻ x, Φ0 (fun a => lA k r z (Matrix.of x) a) * (‖B (σ (twT k r) (σ (Matrix.of x) u))‖₊ : ℝ≥0∞) ^ 2 ∂ν =
      ∫⁻ x, Fu σ z B Φ0 u (fun i j => (twT k r * Matrix.of x) i j) ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    have hx' : Matrix.of (fun i j => (twT k r * Matrix.of x) i j) ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul twT_mem_UH hx
    rw [Fu_on z B Φ0 u _ hx']
    have e0 : (Matrix.of (fun i j => (twT k r * Matrix.of x) i j) : Matrix _ _ ℂ) = twT k r * Matrix.of x := rfl
    have e1 : σ (twT k r * Matrix.of x) u = σ (twT k r) (σ (Matrix.of x) u) := by
      rw [hσ.1.2 _ twT_mem_UH _ hx]; rfl
    have e2 : (fun a => lA k r z (twT k r * Matrix.of x) a) = (fun a => lA k r z (Matrix.of x) a) :=
      funext fun a => lA_twT hz _ a
    rw [e0, e1, e2, Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]
  have E2 : ∫⁻ x, Φ0 (fun a => lA k r z (Matrix.of x) a) * (‖B (σ (Matrix.of x) u)‖₊ : ℝ≥0∞) ^ 2 ∂ν =
      ∫⁻ x, Fu σ z B Φ0 u x ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [Fu_on z B Φ0 u x hx, Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]
  rw [E1, E2, key]

end Formalism.MainNotions.S.Pv.Mom
end
end

section
set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open NumberField Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Bridge Formalism.MainNotions.LowestKTypeMultiplicity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem scale_turn (D : D7) :
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) * -Complex.I = cOfDpsi ((kaS D : ℝ) : ℂ) := by
  unfold cOfDpsi kaS gg
  push_cast
  ring

def LowKOneAt (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → IsHCParam lam' →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) lam' σ → ∀ S S' : Submodule ℂ H,
        IsKTypeOf (epsSH D.R) σ (lowK (epsSH D.R) lam') S → IsKTypeOf (epsSH D.R) σ (lowK (epsSH D.R) lam') S' → S = S'

theorem lowKOneAt_of_mult (h : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne) (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) :
    LowKOneAt D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  fun _ τ lam' _ hHC H _ _ σ hDS S S' h1 h2 => h _ _ _ H σ hHC hDS S S' h1 h2

theorem momNorm'_of_at (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : LowKOneAt D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) (hQ : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv)
    (hLN : Formalism.MainNotions.S.Pv.QuotUniq.QuotLeftNorm) :
    MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn := by
  intro hH τ w w' θ W hW lam' hl A hA hT hT'
  have hW' := hW
  obtain ⟨hc1, -, hz, -, hTz, -, hG, hUW, -, -, -, hN, hq, -⟩ := hW'
  have hTpos : 0 < Tz D.R.k D.R.rS W.z := by rw [hTz]; exact hT
  have hA' := hA
  obtain ⟨hHC, hDSH, hB, -, hv0s, hv0ne, ⟨PS, hPS, hv0low⟩, hcN, hl2, -, -⟩ := hA'
  obtain ⟨-, hπiso, -⟩ := rp_repOfHC _ _ W.z _ W.Wp W.π hz hTpos hc1
  have hNt : Nontrivial W.Wp := by obtain ⟨g, -, hU⟩ := hc1; exact hU.1
  have hσ : IsURepOn (UH (Hpk D.R.k D.R.rS)) A.σ := urep_of_DS hDSH
  obtain ⟨hone, hmul, hiso⟩ := Formalism.MainNotions.LeviCoordinates.discrete_series_unitary_rep hDSH
  have hS : IsHaarOn (Sset D.R.k D.R.rS W.z) (muS W.μW W.μN) := Formalism.MainNotions.BridgeCSB.muSHaar_of D τ w w' θ W hW
  set c1 : ℂ := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) with hc1def
  have hB1 : IsBesselMapSm W.z (psi D.R.k D.R.rS W.z c1) A.σ W.π A.B := hB

  have hDSH2 := hDSH
  obtain ⟨PD, hPD, hDS'⟩ := hDSH2
  obtain ⟨hκ, hκe⟩ := cayley_change hPS hPD
  have hDS : IsDS (epsSH D.R) lam' (fun g => A.σ (PS⁻¹ * g * PS)) := by
    have := dsConjK_proved _ (epsSH D.R) lam' A.H _ _ hκ hDS'
    simp only [hκe] at this
    exact this
  obtain ⟨S0, hS0⟩ := hDS.2.2.2.2.2.1
  have hset : {S | IsKTypeOf (epsSH D.R) (fun g => A.σ (PS⁻¹ * g * PS)) (lowK (epsSH D.R) lam') S} = {S0} := by
    ext S
    constructor
    · intro h; exact hM1 hH τ lam' hl hHC A.H _ hDS S S0 h hS0
    · intro h; rw [Set.mem_singleton_iff.1 h]; exact hS0
  have hv0S : A.v0 ∈ S0 := by
    have h := hv0low
    unfold lowKSub at h
    rw [hset, sSup_singleton] at h
    exact h
  obtain ⟨hfd, hst, hirr, ⟨w0, hw0S, hw0ne, hwt⟩, -⟩ := id hS0
  have := hfd
  have hsm : ∀ u ∈ S0, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u :=
    fun u hu => hSm _ _ (epsSH D.R) lam' A.H A.σ hHC hDSH u ⟨S0, hfd, hu, kstable_Hpk hPS hst⟩
  have hS0ne : S0 ≠ ⊥ := by
    intro hb; rw [hb] at hw0S; exact hw0ne (by simpa using hw0S)

  set m : ℝ := A.cN * (Module.finrank ℂ W.Wp : ℝ) with hm
  have hm0 : 0 < m := mul_pos hcN (by exact_mod_cast Module.finrank_pos)
  set a : ℝ := ‖A.v0‖ / Real.sqrt m with ha
  have hαsq : ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 = ((‖A.v0‖₊ : ℝ≥0∞)) ^ 2 * (ENNReal.ofReal m)⁻¹ := by
    rw [← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq, ← ENNReal.ofReal_inv_of_pos hm0,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, ha, div_pow, Real.sq_sqrt hm0.le, div_eq_mul_inv]
  have hM0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.2 hm0).ne'
  have hMt : ENNReal.ofReal m ≠ ⊤ := ENNReal.ofReal_ne_top
  have hαt : ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hN' := hN
  rw [hN'] at hS hq

  have tw : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u → ∀ Φ0 : (Fin (D.R.rS + 1) → ℝ) → ℝ≥0∞, Measurable Φ0 →
      ∫⁻ x, Φ0 (fun i => lA D.R.k D.R.rS W.z (Matrix.of x) i) *
          (‖(a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) (A.σ (Matrix.of x) u))‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
        ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 *
          ∫⁻ x, Φ0 (fun i => lA D.R.k D.R.rS W.z (Matrix.of x) i) * (‖A.B (A.σ (Matrix.of x) u)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS := by
    intro u hu Φ0 hΦ0
    rw [← twist_lintegral hLN hσ hz hTpos c1 hπiso hB1 (kapN D θ) hG hUW hS hq hu hΦ0, ← lintegral_const_mul' _ _ hαt]
    refine lintegral_congr fun x => ?_
    rw [nnnorm_smul, ENNReal.coe_mul, mul_pow]
    ring
  refine ⟨fun v => (a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) v), PS, w0, ?_, ?_, hPS, ?_, hw0ne, ?_⟩
  · rw [← scale_turn D]
    exact bessel_smul (bessel_twist A.σ hone hmul hiso hz hB1) _
  · intro v hv
    have h1 := tw v hv (fun _ => 1) measurable_const
    simp only [one_mul] at h1
    unfold l2SG
    rw [h1]
    have h2 := hBS hH τ w w' θ W hW lam' hl A hA hT v hv
    unfold l2SG at h2 hl2
    rw [hl2] at h2
    beta_reduce at h2
    rw [hαsq]
    calc (‖A.v0‖₊ : ℝ≥0∞) ^ 2 * (ENNReal.ofReal m)⁻¹ *
          ∫⁻ x, (‖A.B (A.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS
        = (ENNReal.ofReal m)⁻¹ * ((∫⁻ x, (‖A.B (A.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS) *
            (‖A.v0‖₊ : ℝ≥0∞) ^ 2) := by ring
      _ = (ENNReal.ofReal m)⁻¹ * (ENNReal.ofReal m * (‖v‖₊ : ℝ≥0∞) ^ 2) := by rw [h2]
      _ = (‖v‖₊ : ℝ≥0∞) ^ 2 := ENNReal.inv_mul_cancel_left hM0 hMt
  · have hl0 : l1 (lowK (epsSH D.R) lam') (lowK (epsSH D.R) lam') ≤ ((0 : ℕ) : ℝ) := by simp [l1]
    exact Submodule.subset_span ⟨_, _, _, hS0, hw0S, hwt, hl0, hl0⟩
  · intro F hF
    obtain ⟨CF, hCF⟩ := kinv_form hQ laLeftS_proved laRightK_proved hPS hσ hz hTpos c1 hπiso hB1 hG
      (by rw [hN'] at *; exact hS) (by rw [hN'] at *; exact hq) S0 hS0ne hst hirr hsm hF
    have eL : ∫⁻ x, F (fun i => lA D.R.k D.R.rS W.z (Matrix.of x) i) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
        ENNReal.ofReal (‖A.v0‖ ^ 2) * CF := hCF A.v0 hv0S
    rw [eL]
    unfold Emom
    have ew := tw w0 (hsm w0 hw0S) F hF
    have e2 : ∫⁻ x, (fun g => F (fun i => lA D.R.k D.R.rS W.z g i)) (Matrix.of x) *
        (‖(a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) (A.σ (Matrix.of x) w0))‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
        ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 * (ENNReal.ofReal (‖w0‖ ^ 2) * CF) := by
      rw [ew, hCF w0 hw0S]
    erw [e2]
    rw [hl2]
    have hw0p : ENNReal.ofReal (‖w0‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have key : ∀ (M Wn V CF : ℝ≥0∞), M ≠ 0 → M ≠ ⊤ → Wn ≠ 0 → Wn ≠ ⊤ →
        V * CF = M * (Wn⁻¹ * (V * M⁻¹ * (Wn * CF))) := by
      intro M Wn V CF h1 h2 h3 h4
      calc V * CF = (M * M⁻¹) * ((Wn⁻¹ * Wn) * (V * CF)) := by
            rw [ENNReal.mul_inv_cancel h1 h2, ENNReal.inv_mul_cancel h3 h4]; simp
        _ = M * (Wn⁻¹ * (V * M⁻¹ * (Wn * CF))) := by ring
    rw [hαsq, Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]
    exact key _ _ _ _ hM0 hMt hw0p ENNReal.ofReal_ne_top

theorem momNorm'_of (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) (hQ : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv)
    (hLN : Formalism.MainNotions.S.Pv.QuotUniq.QuotLeftNorm) :
    MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  momNorm'_of_at D large₂ C' Cl Cg cb Cu cT CT C0 Cn hBS (lowKOneAt_of_mult hM1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn) hSm hQ hLN

end Formalism.MainNotions.S.Pv.Mom
end
end

section
set_option linter.unusedVariables false

open MeasureTheory

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge

theorem quotRightInv' (hI : PI.QuotInv) (hU : PI.QuotSetU) : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv := by
  intro k r z μG μS νq hz hT hG hS hq κ hκ F hF hFS
  obtain ⟨h1, h2, h3, h4, h5⟩ := hU k r z hz hT
  exact hI (2 * r + k + 1) _ _ μG μS νq ⟨h1, h2, h3, hG, hS, h4 μG hG, h5 μS hS, hq⟩ F hF hFS κ hκ

theorem quotRightInv_closed : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv := quotRightInv' quotient_invariant quotient_measure_unitary_group

theorem momNorm'_closed (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  momNorm'_of D large₂ C' Cl Cg cb Cu cT CT C0 Cn hBS hM1 hSm quotRightInv_closed Formalism.MainNotions.S.Pv.QuotUniq.quotLeftNorm

theorem momNorm'_closed_at (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : LowKOneAt D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  momNorm'_of_at D large₂ C' Cl Cg cb Cu cT CT C0 Cn hBS hM1 hSm quotRightInv_closed Formalism.MainNotions.S.Pv.QuotUniq.quotLeftNorm

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ)

def BesselSchurF' : Prop :=
  ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => BesselSchur' (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn

theorem momF'_of_schur (hBS : BesselSchurF' Fm Cg cb Cu cT CT C0) (hM1 : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomF' Fm Cg cb Cu cT CT C0 :=
  fun Cn => Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i h => momNorm'_closed _ _ _ _ _ _ _ _ _ _ _ h hM1 hSm) (hBS Cn)

theorem momF'_of_schur_at (hBS : BesselSchurF' Fm Cg cb Cu cT CT C0)
    (hM1 : ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => LowKOneAt (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) : MomF' Fm Cg cb Cu cT CT C0 :=
  fun Cn => Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i h => momNorm'_closed_at _ _ _ _ _ _ _ _ _ _ _ h.1 h.2 hSm)
    ((hBS Cn).and (hM1 Cn))

end Fam

end Formalism.MainNotions.S.Pv.Mom
end
end
