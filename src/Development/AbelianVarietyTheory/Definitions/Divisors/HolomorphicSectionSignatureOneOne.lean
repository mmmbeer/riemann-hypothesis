import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.AdelLeftInvAndContinuous
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDefinite
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDictModel

open GlobalTheory.HolDict

section Local

open ReciprocityTheory.ChartRestriction.G.FD

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sgn_sq (q a : ℕ) : sgn q a * sgn q a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem OrthFr.det_ne {Hm x₀ : Mt n} {q : ℕ} (h : OrthFr Hm q x₀) : x₀.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det h.2
  rw [det_mul, h0, mul_zero, det_diagonal] at h1
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.1 h1.symm
  have h2 := sgn_sq q a
  rw [neg_eq_zero, Complex.ofReal_eq_zero] at ha
  simp [ha] at h2

theorem OrthFr.mem {Hm x₀ : Mt n} {q : ℕ} (h : OrthFr Hm q x₀) : x₀ ∈ frDom Hm q := by
  refine ⟨OrthFr.det_ne h, fun i => ?_⟩
  have e : lminor (-(x₀ᴴ * Hm * x₀)) i = ((psgn q i : ℝ) : ℂ) := by
    rw [h.2, diagonal_neg, lminor, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal, psgn,
      ← Fin.prod_univ_eq_prod_range]
    simp
  rw [e, Complex.ofReal_re, psgn, ← Finset.prod_mul_distrib]
  simp [sgn_sq]

theorem mul_mem_frDom {Hm u x : Mt n} {q : ℕ} (hH : Hm.det ≠ 0) (hu : u ∈ Formalism.QuantumDeterminants.UH Hm) (hx : x ∈ frDom Hm q) :
    u * x ∈ frDom Hm q := by
  have hu' : uᴴ * Hm * u = Hm := hu
  have hd : u.det ≠ 0 := fun h0 => hH (by rw [← hu', det_mul, h0, mul_zero])
  refine ⟨by rw [det_mul]; exact mul_ne_zero hd hx.1, fun i => ?_⟩
  have e : (u * x)ᴴ * Hm * (u * x) = xᴴ * Hm * x := by
    conv_rhs => rw [← hu']
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e]
  exact hx.2 i

theorem torEl_mem {Hm x₀ : ι → Mt n} {q : ι → ℕ} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) (s : ι → Fin n → ℝ) :
    torEl x₀ s ∈ UG Hm := by
  intro τ
  have hd : IsUnit (x₀ τ).det := (OrthFr.det_ne (h τ)).isUnit
  have h1 : x₀ τ * (x₀ τ)⁻¹ = 1 := mul_nonsing_inv _ hd
  set d : Mt n := diagonal (fun a => Complex.exp ((s τ a : ℂ) * Complex.I)) with hdd
  have h2 : dᴴ * ((x₀ τ)ᴴ * Hm τ * x₀ τ) * d = (x₀ τ)ᴴ * Hm τ * x₀ τ := by
    rw [(h τ).2, hdd, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    have : star (Complex.exp ((s τ a : ℂ) * Complex.I)) * Complex.exp ((s τ a : ℂ) * Complex.I) = 1 := by
      rw [mul_comm, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
      simp
    simp only [Pi.star_apply]
    linear_combination (-((sgn (q τ) (a : ℕ) : ℝ) : ℂ)) * this
  show (x₀ τ * d * (x₀ τ)⁻¹)ᴴ * Hm τ * (x₀ τ * d * (x₀ τ)⁻¹) = Hm τ
  calc _ = ((x₀ τ)⁻¹)ᴴ * (dᴴ * ((x₀ τ)ᴴ * Hm τ * x₀ τ) * d) * (x₀ τ)⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (x₀ τ * (x₀ τ)⁻¹)ᴴ * Hm τ * (x₀ τ * (x₀ τ)⁻¹) := by
        rw [h2]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1]; simp

theorem HolFn.torus {Hm x₀ : ι → Mt n} {q : ι → ℕ} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {w : ι → Fin n → ℤ}
    {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) (s : ι → Fin n → ℝ) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    f (u * torEl x₀ s) = torCh w s * f u := by
  obtain ⟨P, hP, hfP⟩ := hf
  have hH : ∀ τ, (Hm τ).det ≠ 0 := fun τ h0 => by
    have h1 := (OrthFr.mem (h τ)).2 (Fin.last n)
    have e : lminor (-((x₀ τ)ᴴ * Hm τ * x₀ τ)) (Fin.last n) = (-((x₀ τ)ᴴ * Hm τ * x₀ τ)).det := rfl
    rw [e, det_neg, det_mul, det_mul, h0] at h1
    simp at h1
  have hm : u * torEl x₀ s ∈ UG Hm := fun τ => by
    have h1 : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
    have h2 : (torEl x₀ s τ)ᴴ * Hm τ * torEl x₀ s τ = Hm τ := torEl_mem h s τ
    show (u τ * torEl x₀ s τ)ᴴ * Hm τ * (u τ * torEl x₀ s τ) = Hm τ
    conv_rhs => rw [← h2, ← h1]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have key := hP.2 (fun τ => (u τ * x₀ τ : Mt n)) (fun τ => mul_mem_frDom (hH τ) (hu τ) (OrthFr.mem (h τ)))
    (fun τ => diagonal fun a => Complex.exp ((s τ a : ℂ) * Complex.I))
    (fun τ => ⟨by rw [det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun _ _ => Complex.exp_ne_zero _,
      fun a c hac => diagonal_apply_ne _ hac.ne'⟩)
  rw [hfP _ hm, hfP _ hu]
  simp only [diagonal_apply_eq] at key
  refine Eq.trans (congrArg P (funext fun τ => ?_)) key
  show u τ * (x₀ τ * _ * (x₀ τ)⁻¹) * x₀ τ = u τ * x₀ τ * _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ (OrthFr.det_ne (h τ)).isUnit, Matrix.mul_one,
    Matrix.mul_assoc]

theorem weight_eq_zero_of_const {Hm x₀ : ι → Mt n} {q : ι → ℕ} (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {w : ι → Fin n → ℤ}
    (hf : HolFn Hm q x₀ w fun _ => 1) (s : ι → Fin n → ℝ) : torCh w s = 1 := by
  have := HolFn.torus h hf s (u := 1) (fun τ => by show (1 : Mt n)ᴴ * _ * 1 = _; simp)
  simpa using this.symm


def H11 : Unit → Mt 2 := fun _ => !![1, 0; 0, -1]

def x11 : Unit → Mt 2 := fun _ => !![0, 1; 1, 0]






theorem exp_one_one (z : ℂ) : (NormedSpace.exp (z • (1 : Mt 1)) : Mt 1) 0 0 = Complex.exp z := by
  have : z • (1 : Mt 1) = diagonal fun _ => z := by
    ext a b
    fin_cases a; fin_cases b; simp
  rw [this, Matrix.exp_diagonal, diagonal_apply_eq, Pi.coe_exp, Complex.exp_eq_exp_ℂ]

theorem der_pow (k : ℕ) (z : ℂ) (u : Unit → Mt 1) :
    der () (z • (1 : Mt 1)) (fun v => v () 0 0 ^ k) u = k * z * u () 0 0 ^ k := by
  have e : (fun t : ℝ => (fun v : Unit → Mt 1 => v () 0 0 ^ k)
      (u * (Pi.mulSingle () (NormedSpace.exp (t • z • (1 : Mt 1))) : Unit → Mt 1))) =
      fun t : ℝ => u () 0 0 ^ k * Complex.exp (k * z * t) := by
    funext t
    have h1 : t • z • (1 : Mt 1) = ((t : ℂ) * z) • (1 : Mt 1) := by
      rw [← smul_assoc, Complex.real_smul]
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same, Matrix.mul_apply, Fin.sum_univ_one, h1]
    rw [exp_one_one, mul_pow, ← Complex.exp_nat_mul]
    ring_nf
  unfold der
  rw [e]
  have h := (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul ((k : ℂ) * z)).cexp).const_mul (u () 0 0 ^ k)
  refine h.deriv.trans ?_
  simp
  ring


end Local

section Adelic

variable {D : D7}

theorem fix_iff (τ : D.host.E →+* ℂ) :
    τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD ↔ ∃ ρ, τ = tauE D ρ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 τ
  have h1 : D.host.galE (D.host.sigmaOf g) = g :=
    (D.host.gal).apply_symm_apply g
  refine Iff.trans ?_ (Formalism.L2.Geo.exists_tauEmb_iff D g).symm
  conv_rhs => rw [← h1]
  refine Iff.trans ?_ (D.host.galE_mem_Psi_iff _).symm
  exact ⟨fun h => D.host.φ₀.injective h, fun h => congrArg D.host.φ₀ h⟩


end Adelic

section Dict

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member

variable {D : D7}

theorem tauE_inj : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem gram_model (V : HSp D) (ρ : D.what₂.Tau) (x : Mt V.rank) :
    ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) (-V.gramᵀ) x = (-(xᴴ * gramAt D V ρ * x))ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, transpose_apply, Matrix.neg_apply, Matrix.mul_apply, conjTranspose_apply,
    gramAt, map_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

open Classical in

def plOf {β : Type} (b : β) (f : D.what₂.Tau → β) (τ : D.host.E →+* ℂ) : β :=
  if h : ∃ ρ, τ = tauE D ρ then f h.choose else b







end Dict

section Forms

variable {D : D7}

set_option maxHeartbeats 1600000 in

theorem exists_isReg (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (h : FinPair V μ 𝓕) : ∃ ρ, IsReg V μ 𝓕 ρ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := h.haar
  have := h.right
  have key : ∀ ν : Measure (AutQ V), AutomorphicL2Unitary.quotMeasure (GQ V) μ = ν →
      ∃ ρ : GA D V →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν), (∀ g F, ∀ᵐ x ∂μ, ρ g F (autMk V x) = F (autMk V (x * g))) ∧
        (∀ g F, ‖ρ g F‖ = ‖F‖) ∧ ∀ F, Continuous fun g => ρ g F := by
    rintro ν rfl
    refine ⟨AutomorphicL2Unitary.R (GQ V) μ, fun g F => ?_, fun g F => ?_, fun F => ?_⟩
    · exact AutomorphicL2Unitary.lift_R (Γ := GQ V) (μ := μ) g F
    · exact AutomorphicL2Unitary.norm_R (Γ := GQ V) (μ := μ) g F
    · exact AutomorphicL2Unitary.continuous_R (Γ := GQ V) (μ := μ) F
  have e : AutomorphicL2Unitary.quotMeasure (GQ V) μ = nuQ V μ 𝓕 := AutomorphicL2Unitary.quotMeasure_eq (Γ := GQ V) (μ := μ) h.fd
  obtain ⟨ρ, a, b, c⟩ := key _ e
  exact ⟨ρ, { val := a, iso := b, cont := c }⟩



end Forms

end GlobalTheory.HolDictModel
