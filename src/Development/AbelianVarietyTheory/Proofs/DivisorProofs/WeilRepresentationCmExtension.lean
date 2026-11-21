import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleSupNeTop
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEmbeddingAtEveryPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForClosure

section
noncomputable section

namespace GlobalTheory.ThK.PlaneEv

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {n d d₁ : ℕ}

def idx (hd : d = d₁ + 2) : Fin n × Fin d ≃ Fin n × Fin d₁ ⊕ Fin n × Fin 2 :=
  ((Equiv.refl (Fin n)).prodCongr ((finCongr hd).trans finSumFinEquiv.symm)).trans (Equiv.prodSumDistrib _ _ _)

def ins0 {R : Type} [Zero R] (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → R) : Fin n × Fin d → R :=
  fun k => Sum.elim x 0 (idx hd k)

section Ins

variable {R : Type} (hd : d = d₁ + 2)

@[simp] theorem planeZeroInsertion_apply_inl [Zero R] (x : Fin n × Fin d₁ → R) (p : Fin n × Fin d₁) :
    ins0 hd x ((idx hd).symm (Sum.inl p)) = x p := by
  simp [ins0]

@[simp] theorem planeZeroInsertion_apply_inr [Zero R] (x : Fin n × Fin d₁ → R) (p : Fin n × Fin 2) :
    ins0 hd x ((idx hd).symm (Sum.inr p)) = 0 := by
  simp [ins0]

theorem ins0_zero [Zero R] : ins0 hd (0 : Fin n × Fin d₁ → R) = 0 := by
  funext k; simp only [ins0]; rcases idx hd k with p | p <;> rfl

theorem ins0_add [AddZeroClass R] (x y : Fin n × Fin d₁ → R) : ins0 hd (x + y) = ins0 hd x + ins0 hd y := by
  funext k; simp only [ins0, Pi.add_apply]; rcases idx hd k with p | p <;> simp

theorem ins0_smul {S : Type} [Zero R] [SMulZeroClass S R] (c : S) (x : Fin n × Fin d₁ → R) :
    ins0 hd (c • x) = c • ins0 hd x := by
  funext k; simp only [ins0, Pi.smul_apply]; rcases idx hd k with p | p <;> simp

theorem ins0_map {R' : Type} [Zero R] [Zero R'] (g : R → R') (hg : g 0 = 0) (x : Fin n × Fin d₁ → R) :
    (fun k => g (ins0 hd x k)) = ins0 hd (fun p => g (x p)) := by
  funext k; simp only [ins0]; rcases idx hd k with p | p <;> simp [hg]

theorem ins0_dotProduct [NonUnitalNonAssocSemiring R] (x : Fin n × Fin d₁ → R) (b : Fin n × Fin d → R) :
    ins0 hd x ⬝ᵥ b = x ⬝ᵥ fun p => b ((idx hd).symm (Sum.inl p)) := by
  simp only [dotProduct]
  rw [← (idx hd).symm.sum_comp, Fintype.sum_sum_type]
  simp

theorem ins0_dotProduct_ins0 [NonUnitalNonAssocSemiring R] (x y : Fin n × Fin d₁ → R) :
    ins0 hd x ⬝ᵥ ins0 hd y = x ⬝ᵥ y := by
  rw [ins0_dotProduct]; simp

end Ins

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def insertZerosCLM (hd : d = d₁ + 2) :
    (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := ins0 hd
      map_add' := ins0_add hd
      map_smul' := fun c x => ins0_smul hd c x }

@[simp] theorem planeZeroInsertionLinear_apply (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) :
    insertZerosCLM F hd x = ins0 hd x := rfl

theorem norm_le_ins0 (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) : ‖x‖ ≤ ‖ins0 hd x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => ?_
  have := norm_le_pi_norm (ins0 hd x) ((idx hd).symm (Sum.inl p))
  rwa [planeZeroInsertion_apply_inl] at this

def ei (hd : d = d₁ + 2) : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) :=
  SchwartzMap.compCLM ℂ (insertZerosCLM F hd).hasTemperateGrowth
    ⟨1, 1, fun x => by
      have := norm_le_ins0 F hd x
      simp only [planeZeroInsertionLinear_apply, pow_one, one_mul]
      linarith [norm_nonneg (ins0 hd x)]⟩

@[simp] theorem ei_apply (hd : d = d₁ + 2) (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) :
    ei F hd f x = f (ins0 hd x) := rfl

variable {F}

def ev (hd : d = d₁ + 2) (v : Pl F) : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ :=
  LinearMap.funLeft ℂ ℂ (ins0 hd)

@[simp] theorem ev_apply (hd : d = d₁ + 2) (v : Pl F) (φ : (Fin n × Fin d → Fv F v) → ℂ) (x : Fin n × Fin d₁ → Fv F v) :
    ev hd v φ x = φ (ins0 hd x) := rfl

variable (F) in

def evA (hd : d = d₁ + 2) : Fn F n d →ₗ[ℂ] Fn F n d₁ := LinearMap.funLeft ℂ ℂ (ins0 hd)

@[simp] theorem evA_apply (hd : d = d₁ + 2) (Φ : Fn F n d) (x : Fin n × Fin d₁ → AF F) : evA F hd Φ x = Φ (ins0 hd x) := rfl

theorem ei_ne_zero (hd : d = d₁ + 2) : ei (n := n) F hd ≠ 0 := by
  classical
  intro h
  let b : ContDiffBump (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have h1 := congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) => T (hs.toSchwartzMap hc) 0) h
  have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  simp [ins0_zero, h2] at h1

theorem evA_pure (hd : d = d₁ + 2) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) :
    evA F hd (pure f φ) = pure (ei F hd f) fun v => ev hd v (φ v) := by
  funext x
  simp only [evA_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, ei_apply, ev_apply]
  rw [ins0_map hd (evI F) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : AF F).1 = 0
    rw [show (0 : AF F).1 = 0 from rfl, map_zero])]
  congr 1
  congr 1
  funext v
  rw [ins0_map hd (evFin F v) (map_zero _)]

end GlobalTheory.ThK.PlaneEv
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

namespace GlobalTheory.SympRight

theorem hTens_eq_trace' {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    hTens c JA JB x y = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem symp_mul_transpose_right : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S)
    {α β β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β'] [DecidableEq β']
    (JA : Matrix α α S) (JB : Matrix β β S) (Q : Matrix β β' S) (z z' : Matrix α β' S),
    symp c ξ JA JB (z * Qᵀ) (z' * Qᵀ) = symp c ξ JA (Qᵀ * JB * Q.map c) z z' := by
  intro R S _ _ _ c ξ α β β' _ _ _ _ _ _ JA JB Q z z'
  simp only [symp, hTens_eq_trace']
  congr 2
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Q]
  simp only [Matrix.mul_assoc]

end GlobalTheory.SympRight
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Matrix

namespace GlobalTheory.LocalOpsW

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E}
    {om : Rep σ X W} (hWeil : M.IsWeil ψ χX χW om) (v : Pl F) (x : UA σ X.J × UA σ W.J)
    (hx1 : x.1 ∈ UAt σ X (evFin F v)) (hx2 : x.2 ∈ UAt σ W (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin n × Fin d → AF F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    om x (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om x Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  set w := M.co.e.symm (p, q) with hw
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h1 : u • (mat x.1 - 1) = 0 := hx1 u hu
  have h2 : u • (mat x.2 - 1) = 0 := hx2 u hu
  have e1 : mat x.1 * (u • w) = u • w := by
    have : mat x.1 * (u • w) - u • w = (u • (mat x.1 - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h1, Matrix.zero_mul, sub_eq_zero] at this
    exact this
  have e2 : (u • w) * (mat x.2)ᵀ = u • w := by
    have : (u • w) * (mat x.2)ᵀ - u • w = w * (u • (mat x.2 - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : GlobalTheory.WeilM.actAB (cA σ) x (u • w) = u • w := by
    simp only [GlobalTheory.WeilM.actAB]
    have := e1
    simp only [mat] at this e2
    rw [this, e2]
  have h3 := hW.impl x (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

theorem acts_exists {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E}
    {om : Rep σ X W} (hstd : IsStd ψ) (hWeil : M.IsWeil ψ χX χW om) (v : Pl F) (x : UA σ X.J × UA σ W.J)
    (hx1 : x.1 ∈ UAt σ X (evFin F v)) (hx2 : x.2 ∈ UAt σ W (evFin F v))
    (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om x) φ φ₁ := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  set T := om x with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres x Φ hΦ
  have hcomm := comm_off hWeil v x hx1 hx2
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ x Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin n × Fin d → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, GlobalTheory.ThK.LocalOps.schr_trans, GlobalTheory.ThK.LocalOps.schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  refine ⟨(R 0)⁻¹ • fun t => T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin n × Fin d → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← GlobalTheory.ThK.LocalOps.liftV_one_mul]
      ring
    have hpat : At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [tens, hpdef, Pi.smul_apply, smul_eq_mul]
    field_simp

theorem ops : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F,
        (∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
          ∃! φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (g, h)) φ φ₁) ∧
        ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
          ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ φ₁', Acts (evFin F v) (om (g, h)) φ φ₁ →
          Acts (evFin F v) (om (g, h)) φ' φ₁' → Acts (evFin F v) (om (g, h)) (φ + φ') (φ₁ + φ₁') := by
  intro _hP F E _ _ _ _ _ σ _hCM n d X W M ψ χX χW om hstd _ _ _ _ _ _ _ _ hWeil v
  have hex : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, h)) φ φ₁ :=
    fun g hg h hh φ hφ => acts_exists hstd hWeil v (g, h) hg hh φ hφ
  refine ⟨fun g hg h hh φ hφ => ?_, fun g hg h hh φ hφ φ' hφ' φ₁ φ₁' h1 h1' => ?_⟩
  · obtain ⟨φ₁, h1, h2⟩ := hex g hg h hh φ hφ
    exact ⟨φ₁, ⟨h1, h2⟩, fun φ₂ hφ₂ => GlobalTheory.ThK.LocalOps.acts_unique v _ hφ hφ₂.2 h2⟩
  · have := GlobalTheory.ThK.LocalOps.acts_lin v (om (g, h)) (hex g hg h hh) hφ hφ' h1 h1' 1 1
    simpa only [one_smul] using this

end GlobalTheory.LocalOpsW

end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct Matrix GlobalTheory.VacAny GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitTransportPair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

omit [NumberField E] in
theorem isUnit_det_map {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (hJ : J.det ≠ 0) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    IsUnit (J.map t).det := by
  rw [show J.map t = (t : E →+* Fv F v).mapMatrix J from rfl, ← RingHom.map_det]
  exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 hJ)

def pairCo (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (u : Matrix (Fin n) (Fin d) (AE F E)) : Matrix (Fin n) (Fin d) (Fv F v) :=
  -(J.map t * u.map (piW (t.comp σ)) * (K.map t)ᵀ)

omit [NumberField E] in
theorem pairCo_eq_zero (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (h : u.map (piW (t.comp σ)) = 0) : pairCo σ J K t u = 0 := by
  unfold pairCo; rw [h]; simp

theorem exists_coords (hcm : IsCMExt F E σ) (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E)
    (hJ : J.det ≠ 0) (hK : K.det ≠ 0) (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ uT uM : Matrix (Fin n) (Fin d) (Fv F v) →+ Matrix (Fin n) (Fin d) (AE F E),
      (∀ Y, At (evFin F v) (uT Y) ∧ (uT Y).map (piW (t.comp σ)) = 0 ∧ (uT Y).map (piW t) = Y) ∧
      (∀ z, At (evFin F v) (uM z) ∧ (uM z).map (piW t) = 0 ∧ pairCo σ J K t (uM z) = z) ∧
      (∀ u, At (evFin F v) u → ∃ Y z, u = uT Y + uM z) := by
  have hP : IsUnit (J.map t).det := isUnit_det_map J hJ t
  have hQ : IsUnit ((K.map t)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_det_map K hK t
  set P := J.map t with hPdef
  set Q := (K.map t)ᵀ with hQdef
  let L := GlobalTheory.LinBarCoords.liftM σ hcm (m := Fin n) (n := Fin d) v t
  let uT : Matrix (Fin n) (Fin d) (Fv F v) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun Y => L (Y, 0)) (fun Y Y' => by rw [← map_add, Prod.mk_add_mk, add_zero])
  let uM : Matrix (Fin n) (Fin d) (Fv F v) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun z => L (0, -(P⁻¹ * z * Q⁻¹))) (fun z z' => by
      rw [Matrix.mul_add, Matrix.add_mul, neg_add, ← map_add, Prod.mk_add_mk, add_zero])
  have hco : ∀ u, pairCo σ J K t u = -(P * u.map (piW (t.comp σ)) * Q) := fun u => rfl
  have hTc : ∀ Y, (uT Y).map (piW (t.comp σ)) = 0 := fun Y => GlobalTheory.LinBarCoords.liftM_snd σ hcm v t _
  have hTt : ∀ Y, (uT Y).map (piW t) = Y := fun Y => GlobalTheory.LinBarCoords.liftM_fst σ hcm v t _
  have hMc : ∀ z, (uM z).map (piW (t.comp σ)) = -(P⁻¹ * z * Q⁻¹) := fun z => GlobalTheory.LinBarCoords.liftM_snd σ hcm v t _
  have hMt : ∀ z, (uM z).map (piW t) = 0 := fun z => GlobalTheory.LinBarCoords.liftM_fst σ hcm v t _
  have hTa : ∀ Y, At (evFin F v) (uT Y) := fun Y => GlobalTheory.LinBarCoords.liftM_at σ hcm v t _
  have hMa : ∀ z, At (evFin F v) (uM z) := fun z => GlobalTheory.LinBarCoords.liftM_at σ hcm v t _
  refine ⟨uT, uM, fun Y => ⟨hTa Y, hTc Y, hTt Y⟩, fun z => ⟨hMa z, hMt z, ?_⟩, fun u hu => ?_⟩
  · have e1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
    have e2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQ
    rw [hco, hMc, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    simp only [← Matrix.mul_assoc, e1, Matrix.one_mul]
    simp only [Matrix.mul_assoc, e2, Matrix.mul_one]
  · refine ⟨u.map (piW t), pairCo σ J K t u, ?_⟩
    have hd : At (evFin F v) (u - (uT (u.map (piW t)) + uM (pairCo σ J K t u))) := by
      intro c hc
      rw [smul_sub, smul_add, hu c hc, hTa _ c hc, hMa _ c hc, add_zero, sub_zero]
    refine (sub_eq_zero.1 (GlobalTheory.LinBarCoords.eq_zero_of_at σ hcm v t hd ?_ ?_))
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTt, hMt, add_zero, sub_self]
    · rw [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _), hTc, hMc, zero_add, hco, Matrix.mul_neg, Matrix.neg_mul,
        neg_neg, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, sub_self]

theorem symp_coords (hcm : IsCMExt F E σ) (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hK : ∀ i j, σ (K j i) = -K i j) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) :
    evFin F v (symp (cA σ) (-1) (incM F J) (incM F K) x u) =
      ∑ i, ∑ j, (x.map (piW t)) i j * pairCo σ J K t u i j - ∑ i, ∑ j, pairCo σ J K t x i j * (u.map (piW t)) i j :=
  GlobalTheory.T.local_lattice_hermitian_skew hcm v t J K hJ hK x u hx

variable {X : Spc F E n} {W : Spc F E d}

open GlobalTheory.LinWAt in

theorem exists_isLinW (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hstd : IsStd ψ)
    (hXh : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0) (hWh : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ), M.IsLinW ψ t 1 1 ι := by
  obtain ⟨uT, uM, hT, hM, hspan⟩ := exists_coords hcm X.J W.J hXd hWd v t
  have hsymp := symp_coords hcm X.J W.J hXh hWh v t
  have hψc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hstd.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v
  have hcoT : ∀ Y, pairCo σ X.J W.J t (uT Y) = 0 := fun Y => pairCo_eq_zero _ _ t _ (hT Y).2.1
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.lagrangian_decomposition_weil (GlobalTheory.LatVac.psiAt ψ v) hψc hψ1
    ((GlobalTheory.LatVac.locCo M.co v).comp uT) ((GlobalTheory.LatVac.locCo M.co v).comp uM)
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1, hcoT, hcoT]
      simp)
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hM z).1, (hM z).2.1, (hM z').2.1]
      simp)
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1, (hT Y).2.2, (hM z).2.2, hcoT, (hM z).2.1]
      simp)
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj M.co v w
      obtain ⟨Y, z, rfl⟩ := hspan u hu
      exact ⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add]⟩)
  have hφ₁ : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hz : z = 0 := by
      have h := hu0
      rw [Matrix.map_add _ (map_add _), (hT Y₀).2.1, zero_add] at h
      rw [← (hM z).2.2]
      exact pairCo_eq_zero _ _ t _ h
    subst hz
    rw [map_zero, add_zero] at e1 ⊢
    rw [co_one, (hT Y₀).2.2, e1]
    exact congrFun (htr Y₀ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hY : Y₀ = 0 := by
      have h := hu1
      rw [Matrix.map_add _ (map_add _), (hM z).2.1, add_zero] at h
      rw [← (hT Y₀).2.2]
      exact h
    subst hY
    rw [map_zero, zero_add] at e1 ⊢
    rw [co_one, e1, GlobalTheory.VacIndic.psi_of_at ψ (at_symp _ _ _ x (uM z) hx), hsymp x (uM z) hx,
      pairCo_eq_zero _ _ t x hx0, (hM z).2.1, (hM z).2.2]
    have h2 := congrFun (hmu z φ hφ) (x.map (piW t))
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2, ← GlobalTheory.LatVac.psiAt_apply]
    congr 2
    simp

theorem shape (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hstd : IsStd ψ)
    (hXh : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0) (hWh : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (χX χW : Chr F E) (om : Rep σ X W) (hWeil : M.IsWeil ψ χX χW om) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t 1 1 ι)
    (g : UA σ X.J) (h : UA σ W.J)
    (hex : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, h)) φ φ₁) :
    ∃ c : ℂ, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (g, h)) φ φ₁ →
      ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), ι φ₁ ((mat g).map (piW t) * Y * ((mat h).map (piW t))ᵀ) = c * ι φ Y := by
  have hψc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hstd.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hstd v
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  have hex' : ∀ φ, ∃ φ₁, φ ∈ SB (Fin n × Fin d → Fv F v) →
      φ₁ ∈ SB (Fin n × Fin d → Fv F v) ∧ Acts (evFin F v) (om (g, h)) φ φ₁ := by
    intro φ
    by_cases hφ : φ ∈ SB (Fin n × Fin d → Fv F v)
    · obtain ⟨φ₁, hφ₁⟩ := hex φ hφ
      exact ⟨φ₁, fun _ => hφ₁⟩
    · exact ⟨0, fun h' => absurd h' hφ⟩
  choose A hA using hex'
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin n × Fin d) v
  have hinv := (hR 0 (Submodule.zero_mem _)).1
  have huniq : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (g, h)) φ φ₁ → φ₁ = A φ :=
    fun φ hφ φ₁ hB => GlobalTheory.UnitWShape.eq_of_tens_eq v R hR0 hinv φ₁ (A φ)
      ((hB R (hR φ hφ)).symm.trans ((hA φ hφ).2 R (hR φ hφ)))
  have hASB : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), A φ ∈ SB (Fin n × Fin d → Fv F v) := fun φ hφ => (hA φ hφ).1
  have hlin : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), ∀ c : ℂ,
      A (c • φ + φ') = c • A φ + A φ' := by
    intro x hx y hy c
    have hz : c • x + y ∈ SB (Fin n × Fin d → Fv F v) := add_mem (Submodule.smul_mem _ c hx) hy
    apply GlobalTheory.UnitWShape.eq_of_tens_eq v R hR0 hinv
    rw [← (hA _ hz).2 R (hR _ hz), GlobalTheory.UnitWShape.tens_add_smul, map_add, map_smul, (hA x hx).2 R (hR x hx),
      (hA y hy).2 R (hR y hy), ← GlobalTheory.UnitWShape.tens_add_smul]
  have atMul : ∀ (P : Matrix (Fin n) (Fin n) (AE F E)) (Q : Matrix (Fin d) (Fin d) (AE F E))
      (γ : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) γ → At (evFin F v) (P * γ * Q) := by
    intro P Q γ hγ u hu
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have hsb : ∀ (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) (φ : (Fin n × Fin d → Fv F v) → ℂ),
      φ ∈ SB (Fin n × Fin d → Fv F v) → schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ SB (Fin n × Fin d → Fv F v) :=
    fun w φ hφ => GlobalTheory.SchrSB.schr_mem_SB ψ hstd.1 v w φ hφ
  have hcov : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      A (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) =
        schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v (mat g * γ * (mat h)ᵀ)) (A φ) := by
    intro γ hγ φ hφ
    have hψ₁ := hsb (GlobalTheory.LatVac.locCo M.co v γ) φ hφ
    apply GlobalTheory.UnitWShape.eq_of_tens_eq v R hR0 hinv
    have e1 := GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v γ hγ φ R (hR φ hφ)
    have e2 := hSplit.impl (g, h) γ _ (hR φ hφ).2
    rw [← (hA _ hψ₁).2 R (hR _ hψ₁), ← e1, e2, (hA φ hφ).2 R (hR φ hφ)]
    exact GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v _ (atMul _ _ γ hγ) (A φ) R (hR _ (hASB φ hφ))

  have hL := hι
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLinW at hL
  simp only [inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at hL
  have hT : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → γ.map (piW (t.comp σ)) = 0 →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ Y,
        ι (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) Y = ι φ (Y + γ.map (piW t)) :=
    fun γ hγ h0 φ hφ Y => hL.trans γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v γ hγ φ) Y
  have hM : ∀ γ : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) γ → γ.map (piW t) = 0 →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x →
        x.map (piW (t.comp σ)) = 0 →
        ι (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) (x.map (piW t)) =
          ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x γ) * ι φ (x.map (piW t)) :=
    fun γ hγ h0 φ hφ x hx hx0 =>
      hL.mult γ hγ h0 φ hφ _ (hsb _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v γ hγ φ) x hx hx0
  obtain ⟨uT, uM, hT', hM', -⟩ := exists_coords hcm X.J W.J hXd hWd v t
  let Lm : (Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) :=
    fun l => Matrix.of fun k j => l (Matrix.single k j 1)
  have hchar : ∀ (l : Matrix (Fin n) (Fin d) (Fv F v) →ₗ[Fv F v] Fv F v) (Y : Matrix (Fin n) (Fin d) (Fv F v)),
      ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) (uT Y) (uM (Lm l))) = GlobalTheory.LatVac.psiAt ψ v (l Y) := by
    intro l Y
    rw [GlobalTheory.VacIndic.psi_of_at ψ (GlobalTheory.LinWAt.at_symp _ _ _ (uT Y) (uM (Lm l)) (hT' Y).1),
      symp_coords hcm X.J W.J hXh hWh v t _ _ (hT' Y).1, (hM' _).2.1, (hM' _).2.2, (hT' Y).2.2,
      GlobalTheory.ShapeUV.linForm_sum l Y, ← GlobalTheory.LatVac.psiAt_apply]
    congr 1
    simp [Lm]
  have hmap : ∀ (τ : E →ₐ[F] Fv F v) (γ : Matrix (Fin n) (Fin d) (AE F E)),
      (mat g * γ * (mat h)ᵀ).map (piW τ) = (mat g).map (piW τ) * γ.map (piW τ) * ((mat h).map (piW τ))ᵀ := by
    intro τ γ
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  have hinvar : ∀ x y : Matrix (Fin n) (Fin d) (AE F E),
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) (mat g * x * (mat h)ᵀ) (mat g * y * (mat h)ᵀ) =
        symp (cA σ) (-1) (incM F X.J) (incM F W.J) x y := by
    intro x y
    have hU : (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J := g.2
    have hU' : (mat h)ᵀ * incM F W.J * (mat h).map (cA σ) = incM F W.J := h.2
    rw [GlobalTheory.SympRight.symp_mul_transpose_right, hU', GlobalTheory.ShapeUV.symp_mul_mul _ _ _ _ _ hU]
  set gt := (mat g).map (piW t) with hgt
  set ht := (mat h).map (piW t) with hht
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt ψ v) hψc hψ1 ι
    (fun φ (Y : Matrix (Fin n) (Fin d) (Fv F v)) => ι (A φ) (gt * Y * htᵀ)) hL.bij
    (fun x hx y hy c => by
      funext Y
      simp only [hlin x hx y hy c, map_add, map_smul, Pi.add_apply, Pi.smul_apply])
    (fun C => schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v (uT C)))
    (fun l => schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v (uM (Lm l))))
    (fun C x hx => by
      refine ⟨hsb _ x hx, ?_, ?_⟩
      · funext Y
        rw [hT _ (hT' C).1 (hT' C).2.1 x hx Y, (hT' C).2.2]
      · funext Y
        have h0 : (mat g * uT C * (mat h)ᵀ).map (piW (t.comp σ)) = 0 := by
          rw [hmap, (hT' C).2.1, Matrix.mul_zero, Matrix.zero_mul]
        rw [hcov _ (hT' C).1 x hx, hT _ (atMul _ _ _ (hT' C).1) h0 (A x) (hASB x hx), hmap, (hT' C).2.2,
          Matrix.mul_add, Matrix.add_mul])
    (fun l x hx => by
      refine ⟨hsb _ x hx, ?_, ?_⟩
      · funext Y
        have hm := hM _ (hM' (Lm l)).1 (hM' _).2.1 x hx (uT Y) (hT' Y).1 (hT' Y).2.1
        rw [(hT' Y).2.2, hchar] at hm
        exact hm
      · funext Y
        have h0 : (mat g * uM (Lm l) * (mat h)ᵀ).map (piW t) = 0 := by
          rw [hmap, (hM' _).2.1, Matrix.mul_zero, Matrix.zero_mul]
        have h1 : (mat g * uT Y * (mat h)ᵀ).map (piW (t.comp σ)) = 0 := by
          rw [hmap, (hT' Y).2.1, Matrix.mul_zero, Matrix.zero_mul]
        have hm := hM _ (atMul _ _ _ (hM' (Lm l)).1) h0 (A x) (hASB x hx) _ (atMul _ _ _ (hT' Y).1) h1
        rw [hinvar, hchar, hmap, (hT' Y).2.2] at hm
        rw [hcov _ (hM' _).1 x hx]
        exact hm)
  refine ⟨c, fun φ hφ φ₁ hact Y => ?_⟩
  rw [huniq φ hφ φ₁ hact]
  exact congrFun (hc φ hφ) Y

theorem one_mem_UAt (X : Spc F E n) (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
  intro u _
  show u • (mat (1 : UA σ X.J) - 1) = 0
  rw [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, smul_zero]

omit [NumberField E] in
theorem mat_one_map (X : Spc F E n) {v : Pl F} (t : E →ₐ[F] Fv F v) : (mat (1 : UA σ X.J)).map (piW t) = 1 := by
  rw [show mat (1 : UA σ X.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_SB_zero (v : Pl F) (n d : ℕ) : ∃ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), f 0 ≠ 0 := by
  obtain ⟨Λ, -, f, hf, hne⟩ := GlobalTheory.T.exists_translation_invariant_functional F v n d
  obtain ⟨Y₀, hY⟩ : ∃ Y₀, f Y₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (by rw [show f = 0 from funext hc, map_zero])
  exact ⟨fun Y => f (Y + Y₀), ⟨hf.1.comp_continuous (continuous_add_const Y₀),
    hf.2.comp_homeomorph (Homeomorph.addRight Y₀)⟩, by simpa using hY⟩

theorem left_action (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hstd : IsStd ψ)
    (hXh : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0) (hWh : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (χX χW : Chr F E) (om : Rep σ X W) (hWeil : M.IsWeil ψ χX χW om) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t 1 1 ι)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) (g' : GL (Fin n) (Fv F v)) (hg' : (mat g).map (piW t) = g'.1)
    (hex : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁) :
    ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (g, 1)) φ φ₁ →
      ι φ₁ = (((chrW χW (t.comp σ) (Matrix.GeneralLinearGroup.det g'))⁻¹ : ℂˣ) : ℂ) •
        GlobalTheory.SplitWeil.om 1 (1 : GL (Fin d) (Fv F v)) g' (ι φ) := by
  obtain ⟨c, hc⟩ := shape hcm M ψ hstd hXh hXd hWh hWd χX χW om hWeil v t ι hι g 1 hex
  simp only [hg', mat_one_map, Matrix.transpose_one, Matrix.mul_one] at hc
  have hJ := isUnit_det_map X.J hXd t
  have g2 : Units.val ((Matrix.GeneralLinearGroup.det g')⁻¹ : (Fv F v)ˣ) = ((mat g).map (piW (t.comp σ))).det := by
    have u := congrArg Matrix.det (GlobalTheory.UnitaryInjAtPlace.unitary_at_components v t g)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hg'] at u
    have u' : (g'.1.det * ((mat g).map (piW (t.comp σ))).det) * (X.J.map t).det = 1 * (X.J.map t).det := by
      linear_combination u
    have u'' := mul_right_cancel₀ hJ.ne_zero u'
    exact Units.inv_eq_of_mul_eq_one_right (u := Matrix.GeneralLinearGroup.det g') u''
  obtain ⟨f, hf, hf0⟩ := exists_SB_zero v n d
  obtain ⟨φ₀, hφ₀, rfl⟩ := hι.bij.surjOn hf
  obtain ⟨φ₀', -, hA₀⟩ := hex φ₀ hφ₀
  have k1 := GlobalTheory.MixedForm.lin_zero hcm M ψ hstd χX χW om hWeil t ι hι g hg (Matrix.GeneralLinearGroup.det g')⁻¹ g2 φ₀ φ₀' hφ₀ hA₀
  have k2 := hc φ₀ hφ₀ φ₀' hA₀ 0
  rw [Matrix.mul_zero, k1] at k2
  have k3 := mul_right_cancel₀ hf0 k2
  intro φ hφ φ₁ hA
  funext Y
  have e := hc φ hφ φ₁ hA ((g'⁻¹).1 * Y)
  rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, ← k3] at e
  have hn : GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g')⁻¹ ^ ((d : ℝ) / 2) =
      GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g') ^ (-(d : ℝ) / 2) := by
    have h0 : 0 ≤ GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g') := NNReal.coe_nonneg _
    rw [neg_div, Real.rpow_neg h0, ← Real.inv_rpow h0]
    simp [GlobalTheory.SplitWeil.nabs]
  rw [e, hn, map_inv]
  simp only [GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, map_one, MonoidHom.one_apply, Units.val_one, inv_one,
    one_mul, Matrix.mul_one, Fintype.card_fin]
  simp only [GlobalTheory.SplitWeil.nabs, map_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul, mul_assoc]

theorem right_action (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hstd : IsStd ψ)
    (hXh : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0) (hWh : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (χX χW : Chr F E) (om : Rep σ X W) (hWeil : M.IsWeil ψ χX χW om) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) (hι : M.IsLinW ψ t 1 1 ι)
    (h : UA σ W.J) (g : GL (Fin d) (Fv F v)) (hg : (mat h).map (piW t) = (GlobalTheory.SplitFlip.invT g).1)
    (hex : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (1, h)) φ φ₁ →
      ι φ₁ = s • GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin n) (Fv F v)) (ι φ) := by
  obtain ⟨c, hc⟩ := shape hcm M ψ hstd hXh hXd hWh hWd χX χW om hWeil v t ι hι 1 h hex
  simp only [hg, mat_one_map, Matrix.one_mul, GlobalTheory.SplitFlip.invT_val, Matrix.transpose_transpose] at hc
  have hc' : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (1, h)) φ φ₁ →
      ∀ Y, ι φ₁ Y = c * ι φ (Y * g.1) := by
    intro φ hφ φ₁ hA Y
    rw [← hc φ hφ φ₁ hA, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨f, hf, hf0⟩ := exists_SB_zero v n d
    obtain ⟨φ₀, hφ₀, rfl⟩ := hι.bij.surjOn hf
    obtain ⟨φ₁, hφ₁, hA⟩ := hex φ₀ hφ₀
    have h1 : φ₁ = 0 := hι.bij.injOn hφ₁ (Submodule.zero_mem _) (by
      funext Y; rw [hc' φ₀ hφ₀ φ₁ hA, map_zero]; simp)
    have h2 : φ₀ = 0 := GlobalTheory.TensUniq.eq_of_tens_eq v φ₀ φ₀ 0 hφ₀ fun r hr => by
      have e := hA r hr
      have z : tens (evFin F v) (0 : (Fin n × Fin d → Fv F v) → ℂ) r = 0 := by
        funext x; simp [tens]
      rw [h1, z] at e
      have e2 := congrArg (om (1, h)⁻¹) e
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero, Module.End.one_apply] at e2
      rw [e2, z]
    exact hf0 (by rw [h2, map_zero]; rfl)
  have h2 : ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g) ^ ((n : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    have := GlobalTheory.SplitWeil.Model.nabs_pos (Matrix.GeneralLinearGroup.det g)
    exact_mod_cast (Real.rpow_pos_of_pos this _).ne'
  refine ⟨c / ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g) ^ ((n : ℝ) / 2) : ℝ) : ℂ),
    div_ne_zero hc0 h2, fun φ hφ φ₁ hA => ?_⟩
  funext Y
  rw [hc' φ hφ φ₁ hA]
  have h1 : GlobalTheory.SplitWeil.nabs (Fv F v) 1 = 1 := by simp [GlobalTheory.SplitWeil.nabs]
  simp only [GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul, map_one, MonoidHom.one_apply, Units.val_one, inv_one,
    one_mul, Matrix.one_mul, Fintype.card_fin, h1, Real.one_rpow, Complex.ofReal_one, mul_one]
  field_simp

theorem transport : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      1 ≤ n → 1 ≤ d → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) →
      ∃ (χ : GL (Fin n) (Fv F v) →* ℂˣ) (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)),
        IsOpen {g | χ g = 1} ∧
        Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) ∧
        ∀ N : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ), N ≤ SB _ → (ThetaSub om v N ↔ GlobalTheory.ThetaGLSub.IsSub χ (N.map ι)) := by
  intro hP F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hstd hXh hXd hWh hWd hrX hrW hχX hχW hWeil _ _ v ⟨t⟩
  obtain ⟨ι, hι⟩ := exists_isLinW hcm M ψ hstd hXh hXd hWh hWd v t
  have hloc := (GlobalTheory.LocalOpsW.ops hP F E σ hcm n d X W M ψ χX χW om hstd hXh hXd hWh hWd hrX hrW hχX hχW hWeil v).1
  have hex : ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (om (g, h)) φ φ₁ :=
    fun g hg h hh φ hφ => (hloc g hg h hh φ hφ).exists
  have surjX : ∀ g' : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), (mat g).map (piW t) = g'.1 := by
    intro g'
    have herm : ∀ i j, σ (X.J j i) = algebraMap F E 1 * X.J i j := fun i j => by
      rw [map_one, one_mul]; exact hXh i j
    exact ⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t X 1 herm (isUnit_det_map _ hXd t) g',
      GlobalTheory.SplitUnitLift.liftU_piW hcm t X.J 1 herm (isUnit_det_map _ hXd t) g'⟩
  have surjW : ∀ g' : GL (Fin d) (Fv F v), ∃ g ∈ UAt σ W (evFin F v), (mat g).map (piW t) = g'.1 := by
    intro g'
    have herm : ∀ i j, σ (W.J j i) = algebraMap F E (-1) * W.J i j := fun i j => by
      rw [map_neg, map_one, neg_one_mul]; exact hWh i j
    exact ⟨_, GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t W (-1) herm (isUnit_det_map _ hWd t) g',
      GlobalTheory.SplitUnitLift.liftU_piW hcm t W.J (-1) herm (isUnit_det_map _ hWd t) g'⟩
  have hνs : GlobalTheory.SmGL.IsSmoothChar (chrW χW (t.comp σ)) :=
    GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous _ (GlobalTheory.ChrWSmooth.continuous_chrW hχW.1 _)
  set χ : GL (Fin n) (Fv F v) →* ℂˣ := GlobalTheory.SmGL.detChar (Fin n) (chrW χW (t.comp σ)) with hχ
  have hχv : ∀ g, χ g = chrW χW (t.comp σ) (Matrix.GeneralLinearGroup.det g) := fun g => rfl
  have hbij := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι
  have hinj := hbij.injOn
  have hmaps : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ι φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) (Fv F v)) :=
    fun φ hφ => hbij.mapsTo hφ
  refine ⟨χ, ι, ?_, hbij, ?_⟩
  · have := hνs.detChar (n := Fin n)
    exact this
  intro N hN

  have hAugSB : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    rw [augAt, Submodule.span_le]
    rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have hVsc : ∀ g ∈ UAt σ X (evFin F v), ∀ g' : GL (Fin n) (Fv F v), (mat g).map (piW t) = g'.1 →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁, Acts (evFin F v) (om (g, 1)) φ φ₁ →
        ι (φ₁ - φ) = (((χ g')⁻¹ : ℂˣ) : ℂ) • (GlobalTheory.SplitWeil.om 1 1 g' (ι φ) - (χ g' : ℂ) • ι φ) := by
    intro g hg g' hg' φ hφ φ₁ hA
    rw [map_sub, left_action hcm M ψ hstd hXh hXd hWh hWd χX χW om hWeil v t ι hι g hg g' hg'
      (hex g hg 1 (one_mem_UAt W v)) φ hφ φ₁ hA, smul_sub, smul_smul, hχv]
    simp
  have hmapAug : (augAt om v).map ι = GlobalTheory.ThetaGLSub.aug d χ := by
    apply le_antisymm
    · rw [augAt, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩, rfl⟩
      have e := hVsc g hg (Matrix.GeneralLinearGroup.map (piW t) g.1) rfl φ hφ φ₁ hA
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ι φ, hmaps φ hφ, rfl⟩)
    · rw [GlobalTheory.ThetaGLSub.aug, Submodule.span_le]
      rintro _ ⟨g', Φ, hΦ, rfl⟩
      obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hΦ
      obtain ⟨g, hg, hgt⟩ := surjX g'
      obtain ⟨φ₁, hφ₁, hA⟩ := hex g hg 1 (one_mem_UAt W v) φ hφ
      have e := hVsc g hg g' hgt φ hφ φ₁ hA
      refine ⟨(χ g' : ℂ) • (φ₁ - φ), Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩), ?_⟩
      rw [map_smul, e, smul_smul]
      simp
  have hiffAug : augAt om v ≤ N ↔ GlobalTheory.ThetaGLSub.aug d χ ≤ N.map ι := by
    rw [← hmapAug]
    refine ⟨Submodule.map_mono, fun h x hx => ?_⟩
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 (h (Submodule.mem_map_of_mem hx))
    rwa [hinj (hN hy) (hAugSB hx) e] at hy

  have hiffW : (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → φ₁ ∈ N) ↔
      ∀ g : GL (Fin d) (Fv F v), ∀ Φ ∈ N.map ι, GlobalTheory.SplitWeil.om 1 g (1 : GL (Fin n) (Fv F v)) Φ ∈ N.map ι := by
    constructor
    · intro H g Φ hΦ
      obtain ⟨φ, hφN, rfl⟩ := Submodule.mem_map.1 hΦ
      obtain ⟨h, hh, hht⟩ := surjW (GlobalTheory.SplitFlip.invT g)
      obtain ⟨φ₁, hφ₁, hA⟩ := hex 1 (one_mem_UAt X v) h hh φ (hN hφN)
      obtain ⟨s, hs0, hs⟩ := right_action hcm M ψ hstd hXh hXd hWh hWd χX χW om hWeil v t ι hι h g hht
        (hex 1 (one_mem_UAt X v) h hh)
      have h1 : ι φ₁ ∈ N.map ι := Submodule.mem_map_of_mem (H h hh φ hφN φ₁ hφ₁ hA)
      rw [hs φ (hN hφN) φ₁ hA] at h1
      exact (Submodule.smul_mem_iff _ hs0).1 h1
    · intro H h hh φ hφN φ₁ hφ₁ hA
      obtain ⟨s, -, hs⟩ := right_action hcm M ψ hstd hXh hXd hWh hWd χX χW om hWeil v t ι hι h
        (GlobalTheory.SplitFlip.invT (Matrix.GeneralLinearGroup.map (piW t) h.1)) (by rw [GlobalTheory.SplitFlip.invT_invT]; rfl)
        (hex 1 (one_mem_UAt X v) h hh)
      have h1 : ι φ₁ ∈ N.map ι := by
        rw [hs φ (hN hφN) φ₁ hA]
        exact Submodule.smul_mem _ _ (H _ _ (Submodule.mem_map_of_mem hφN))
      obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 h1
      rwa [hinj (hN hy) hφ₁ e] at hy
  constructor
  · rintro ⟨h1, -, h3⟩
    refine ⟨hiffAug.1 h1, ?_, hiffW.1 h3⟩
    rintro _ ⟨φ, hφ, rfl⟩
    exact hmaps φ (hN hφ)
  · rintro ⟨h1, -, h3⟩
    exact ⟨hiffAug.2 h1, hN, hiffW.2 h3⟩

end GlobalTheory.SplitTransportPair
end
end

section
namespace GlobalTheory.HoweNonsplit

open GlobalTheory.WeilM GlobalTheory.HoweAdelic

theorem isLocSub_sup {Y G H : Type} [Group G] [Group H] [TopologicalSpace Y] {om : G × H →* Module.End ℂ (Y → ℂ)}
    {N N' : Submodule ℂ (Y → ℂ)} (h : IsLocSub om N) (h' : IsLocSub om N') : IsLocSub om (N ⊔ N') := by
  refine ⟨le_sup_of_le_left h.1, sup_le h.2.1 h'.2.1, fun k φ hφ => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hφ
  rw [map_add]
  exact Submodule.add_mem_sup (h.2.2 k y hy) (h'.2.2 k z hz)

end GlobalTheory.HoweNonsplit
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix Filter Topology
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LocOpsW

theorem extend_hom {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) {G : Type} [Monoid G]
    (T : G →* Module.End ℂ S) : ∃ om' : G →* Module.End ℂ V, ∀ g (s : S), om' g s = (T g s : V) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  set P := S.linearProjOfIsCompl C hC with hPdef
  have hP : ∀ s : S, P s = s := fun s => Submodule.linearProjOfIsCompl_apply_left hC s
  let A : G → Module.End ℂ V := fun g => S.subtype ∘ₗ T g ∘ₗ P + (LinearMap.id - S.subtype ∘ₗ P)
  have hA : ∀ g w, A g w = (T g (P w) : V) + (w - (P w : V)) := fun g w => rfl
  refine ⟨{ toFun := A, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply LinearMap.ext; intro w
    rw [hA, map_one, Module.End.one_apply, Module.End.one_apply]; abel
  · intro x y; apply LinearMap.ext; intro w
    rw [Module.End.mul_apply, hA x, hA y, hA (x * y), map_mul, Module.End.mul_apply]
    have e : P ((T y (P w) : V) + (w - (P w : V))) = T y (P w) := by
      rw [map_add, map_sub, hP, hP, sub_self, add_zero]
    rw [e]; abel
  · intro g s
    show A g s = _
    rw [hA, hP, sub_self, add_zero]

end GlobalTheory.LocOpsW

namespace GlobalTheory.LocOpsW

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem acts_uniq (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    (h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₁) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ :=
  GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ φ₁ φ₂ hφ fun r hr => (h1 r hr).symm.trans (h2 r hr)

theorem loc_hom (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {G : Type} [Monoid G] (Ω : G →* Module.End ℂ ((κ → AF F) → ℂ))
    (hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, Ω x Φ ∈ GlobalTheory.WeilM.schA F κ)
    (hex : ∀ x, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (Ω x) φ φ₁) :
    ∃ T : G →* Module.End ℂ (GlobalTheory.WeilM.SB (κ → Fv F v)),
      ∀ x (φ : GlobalTheory.WeilM.SB (κ → Fv F v)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (Ω x) φ (T x φ) := by
  classical
  let S := GlobalTheory.WeilM.SB (κ → Fv F v)
  let t : G → S → S := fun x φ => ⟨Classical.choose (hex x φ φ.2), (Classical.choose_spec (hex x φ φ.2)).1⟩
  have ht : ∀ x (φ : S), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (Ω x) φ (t x φ) :=
    fun x φ => (Classical.choose_spec (hex x φ φ.2)).2
  have hu : ∀ x (φ ψ : S), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (Ω x) φ ψ → t x φ = ψ :=
    fun x φ ψ h => Subtype.ext (acts_uniq v _ φ.2 (ht x φ) h)
  let L : G → Module.End ℂ S := fun x =>
    { toFun := t x
      map_add' := fun φ ψ => hu x _ _ (by
        have := GlobalTheory.ThK.LocalOps.acts_lin v (Ω x) (hex x) φ.2 ψ.2 (ht x φ) (ht x ψ) 1 1
        simpa using this)
      map_smul' := fun a φ => hu x _ _ (by
        have := GlobalTheory.ThK.LocalOps.acts_lin v (Ω x) (hex x) φ.2 φ.2 (ht x φ) (ht x φ) a 0
        simpa using this) }
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_ }, fun x φ => ht x φ⟩
  · apply LinearMap.ext; intro φ
    show t 1 φ = φ
    refine hu 1 φ φ ?_
    intro r _
    rw [map_one]; rfl
  · intro x y; apply LinearMap.ext; intro φ
    show t (x * y) φ = t x (t y φ)
    refine hu (x * y) φ _ ?_
    rw [map_mul]
    exact GlobalTheory.ThK.LocalOps.acts_mul v (hpres y) (ht y φ) (ht x (t y φ))

end GlobalTheory.LocOpsW

namespace GlobalTheory.LocOpsW

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W} {ψ : AddChar (AF F) ℂ} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W}
    (hW : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass F) ψ M.co (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)) om)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)
    (hx1 : x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v)) (hx2 : x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin n × Fin d → AF F) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d)) :
    om x (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (om x Φ) := by
  set w := M.co.e.symm (p, q) with hw
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h1 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 - 1) = 0 := hx1 u hu
  have h2 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2 - 1) = 0 := hx2 u hu
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 * (u • w) = u • w := by
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 * (u • w) - u • w = (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.1 - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h1, Matrix.zero_mul, sub_eq_zero] at this
    exact this
  have e2 : (u • w) * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2)ᵀ = u • w := by
    have : (u • w) * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2)ᵀ - u • w = w * (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x.2 - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
    exact this
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) x (u • w) = u • w := by
    simp only [GlobalTheory.WeilM.actAB]
    have := e1
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] at this e2
    rw [this, e2]
  have h3 := hW.impl x (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h3
  exact h3

theorem acts_exists {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W} {ψ : AddChar (AF F) ℂ} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W}
    (hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (hW : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass F) ψ M.co (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)) om)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)
    (hx1 : x.1 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ X (evFin F v)) (hx2 : x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ W (evFin F v))
    (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) :
    ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om x) φ φ₁ := by
  set T := om x with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres x Φ hΦ
  have hcomm := comm_off hW v x hx1 hx2
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v ψ T hstd (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace ψ hstd) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ x Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin n × Fin d → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, GlobalTheory.ThK.LocalOps.schr_trans, GlobalTheory.ThK.LocalOps.schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin n × Fin d) v
  refine ⟨(R 0)⁻¹ • fun t => T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ (GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2))
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin n × Fin d → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← GlobalTheory.ThK.LocalOps.liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin n × Fin d → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef, Pi.smul_apply, smul_eq_mul]
    field_simp

end GlobalTheory.LocOpsW

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweAdelic

namespace GlobalTheory.LocOpsW

theorem locRep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    ∃ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
      ∀ g h, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) ∧
        Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hstd hweil v
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hweil
  let ι : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* UA σ X.J × UA σ W.J :=
    (UAtGrp σ X (evFin F v)).subtype.prodMap (UAtGrp σ W (evFin F v)).subtype
  obtain ⟨T, hT⟩ := loc_hom v (om.comp ι) (fun x Φ hΦ => hW.pres (ι x) Φ hΦ)
    (fun x φ hφ => acts_exists hstd hW v (ι x) x.1.2 x.2.2 φ hφ)
  obtain ⟨om', hom'⟩ := extend_hom (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) T
  refine ⟨om', fun g h φ hφ => ?_⟩
  have e := hom' (g, h) ⟨φ, hφ⟩
  refine ⟨?_, ?_⟩
  · rw [show om' (g, h) φ = _ from e]; exact (T (g, h) ⟨φ, hφ⟩).2
  · rw [show om' (g, h) φ = _ from e]; exact hT (g, h) ⟨φ, hφ⟩

end GlobalTheory.LocOpsW
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweAdelic
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweNonsplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def cv (σ : E →ₐ[F] E) (v : Pl F) : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v ⊗[F] E :=
  Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ

instance isModTopEv (v : Pl F) : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩

end GlobalTheory.HoweNonsplit
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweAdelic

noncomputable section

namespace GlobalTheory.HoweNonsplit

theorem howeDualityFor_locOps : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
      ∀ om' : UAtGrp σ X (evFin F v) × UAtGrp σ W (evFin F v) →* Module.End ℂ ((Fin n × Fin d → Fv F v) → ℂ),
        (∀ g h, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' (g, h) φ ∈ SB (Fin n × Fin d → Fv F v) ∧
          Acts (evFin F v) (om (g.1, h.1)) φ (om' (g, h) φ)) → GlobalTheory.Published.HoweDualityFor om' := by
  intro hP hHD F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv
  have key := GlobalTheory.HoweLocal.howeDualityFor_closure hP hHD F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hom v hv
  rw [show Subgroup.closure (UAt σ X (evFin F v)) = GlobalTheory.HoweAdelic.UAtGrp σ X (evFin F v) from
      Subgroup.closure_eq (GlobalTheory.HoweAdelic.UAtGrp σ X (evFin F v)),
    show Subgroup.closure (UAt σ W (evFin F v)) = GlobalTheory.HoweAdelic.UAtGrp σ W (evFin F v) from
      Subgroup.closure_eq (GlobalTheory.HoweAdelic.UAtGrp σ W (evFin F v))] at key
  exact key

end GlobalTheory.HoweNonsplit
end
end

section
open GlobalTheory.WeilM GlobalTheory.HoweAdelic

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HoweAdelic.TrivSup

theorem trivial_irr (G : Type) [Group G] : (Representation.trivial ℂ G ℂ).IsIrreducible := by
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun h => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ ℂ) (congrArg Subrepresentation.toSubmodule h)
  · rcases eq_bot_or_eq_top (α := Submodule ℂ ℂ) S.toSubmodule with h | h
    · exact Or.inl (Subrepresentation.ext h)
    · exact Or.inr (Subrepresentation.ext h)

theorem trivial_adm (G : Type) [Group G] [TopologicalSpace G] :
    GlobalTheory.PRep.IsAdmissible (Representation.trivial ℂ G ℂ) := by
  refine ⟨fun v => ?_, fun K _ _ => inferInstance⟩
  have : {g : G | Representation.trivial ℂ G ℂ g v = v} = Set.univ := by ext; simp
  rw [this]; exact isOpen_univ

theorem exists_coatom_of_finiteLength {H T : Type} [Group H] [AddCommGroup T] [Module ℂ T] (Θ : Representation ℂ H T)
    (hf : IsFiniteLength (MonoidAlgebra ℂ H) Θ.asModule) (S : Subrepresentation Θ) (hS : S ≠ ⊤) :
    ∃ C : Subrepresentation Θ, IsCoatom C ∧ S ≤ C := by
  obtain ⟨hN, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hf
  have : IsCoatomic (Submodule (MonoidAlgebra ℂ H) Θ.asModule) := inferInstance
  have hc : IsCoatomic (Subrepresentation Θ) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Θ)).isCoatomic_iff.2 this
  obtain h | ⟨C, hC, hle⟩ := hc.eq_top_or_exists_le_coatom S
  · exact absurd h hS
  · exact ⟨C, hC, hle⟩

end GlobalTheory.HoweAdelic.TrivSup

namespace GlobalTheory.HoweAdelic

open TrivSup in

theorem sup_ne_SB_of_howeDuality : ∀ {Y G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace Y]
    (om : G × H →* Module.End ℂ (Y → ℂ)), GlobalTheory.Published.HoweDualityFor om → (∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y) →
    ∀ N N', IsLocSub om N → IsLocSub om N' → N ≠ SB Y → N' ≠ SB Y → N ⊔ N' ≠ SB Y := by
  intro Y G H _ _ _ _ _ om hHD hom N N' hN hN' hNe hN'e hsup
  obtain ⟨⟨T, _, _, Θ, p, ⟨hpair, hsurj, hker⟩, -, hfl, huniq⟩, -⟩ :=
    hHD ℂ (Representation.trivial ℂ G ℂ) (trivial_irr G) (trivial_adm G)
  let q : SB Y →ₗ[ℂ] T := (TensorProduct.lid ℂ T).toLinearMap ∘ₗ p
  have hqsurj : Function.Surjective q := (TensorProduct.lid ℂ T).surjective.comp hsurj
  have hq : ∀ (h : H) (φ φ₁ : SB Y), (φ₁ : Y → ℂ) = om (1, h) φ → q φ₁ = Θ h (q φ) := by
    intro h φ φ₁ e
    simp only [q, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hpair 1 h φ φ₁ e]
    induction p φ using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hkerq : ∀ x : SB Y, q x = 0 → (x : Y → ℂ) ∈ locAug om := by
    intro x hx
    have hp : p x = 0 := by simpa [q] using hx
    by_contra hnot
    let L : Submodule ℂ (SB Y) := (locAug om).comap (SB Y).subtype
    have hxL : L.mkQ x ≠ 0 := by
      rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hnot
    obtain ⟨l, hl⟩ : ∃ l : Module.Dual ℂ (SB Y ⧸ L), l (L.mkQ x) ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hxL ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hall)
    have hf : GlobalTheory.Published.IsLeftHom om (Representation.trivial ℂ G ℂ) (l ∘ₗ L.mkQ) := by
      intro g φ φ₁ e
      have hmem : φ₁ - φ ∈ L := by
        show ((φ₁ - φ : SB Y) : Y → ℂ) ∈ locAug om
        rw [Submodule.coe_sub, e]
        exact Submodule.subset_span ⟨g, φ, φ.2, rfl⟩
      have h0 : L.mkQ (φ₁ - φ) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hmem
      rw [map_sub] at h0
      simp only [LinearMap.comp_apply, Representation.trivial, MonoidHom.one_apply, Module.End.one_apply]
      rw [sub_eq_zero.1 h0]
    exact hl ((hker x).1 hp _ hf)
  have key : ∀ M, IsLocSub om M → M ≠ SB Y →
      ∃ C : Subrepresentation Θ, IsCoatom C ∧ ∀ φ : SB Y, (φ : Y → ℂ) ∈ M → q φ ∈ C.toSubmodule := by
    intro M hM hMne
    obtain ⟨S, hSdef⟩ : ∃ S : Subrepresentation Θ, S.toSubmodule = (M.comap (SB Y).subtype).map q :=
      ⟨⟨(M.comap (SB Y).subtype).map q, by
        rintro h _ ⟨φ, hφ, rfl⟩
        exact ⟨⟨om (1, h) φ, hom _ φ φ.2⟩, hM.2.2 h φ hφ, hq h φ _ rfl⟩⟩, rfl⟩
    have hS : S ≠ ⊤ := by
      intro hS
      apply hMne
      refine le_antisymm hM.2.1 (fun φ hφ => ?_)
      have h1 : q ⟨φ, hφ⟩ ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
      rw [hSdef] at h1
      obtain ⟨ψ, hψ, e⟩ := h1
      have hd := hkerq (⟨φ, hφ⟩ - ψ) (by rw [map_sub, e, sub_self])
      have h2 : φ = (((⟨φ, hφ⟩ : SB Y) - ψ : SB Y) : Y → ℂ) + ψ := by simp
      rw [h2]; exact M.add_mem (hM.1 hd) hψ
    obtain ⟨C, hC, hle⟩ := exists_coatom_of_finiteLength Θ hfl S hS
    refine ⟨C, hC, fun φ hφ => hle (show q φ ∈ S.toSubmodule from ?_)⟩
    rw [hSdef]; exact ⟨φ, hφ, rfl⟩
  obtain ⟨C, hC, hCN⟩ := key N hN hNe
  obtain ⟨C', hC', hCN'⟩ := key N' hN' hN'e
  obtain rfl := huniq C C' hC hC'
  apply hC.1
  refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun t _ => ?_)
  obtain ⟨φ, rfl⟩ := hqsurj t
  have hφ : (φ : Y → ℂ) ∈ N ⊔ N' := by rw [hsup]; exact φ.2
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 hφ
  have h3 : φ = ⟨a, hN.2.1 ha⟩ + ⟨b, hN'.2.1 hb⟩ := Subtype.ext (by simp [e])
  rw [h3, map_add]
  exact C.toSubmodule.add_mem (hCN _ ha) (hCN' _ hb)

end GlobalTheory.HoweAdelic
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweNonsplit

open GlobalTheory.HoweAdelic

theorem unique_maximal : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
      ∀ N N', Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N → Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N' → N = N' := by
  intro hP hHD F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hηX hηW hHX hHW hWeil v hv N N' hN hN'
  obtain ⟨om', hom'⟩ := GlobalTheory.LocOpsW.locRep F E σ n d X W M ψ χX χW om hψ hWeil v
  have hHDv := GlobalTheory.HoweNonsplit.howeDualityFor_locOps hP hHD F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hηX hηW hHX hHW hWeil v hv om' hom'
  have hpres : ∀ x, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' x φ ∈ SB (Fin n × Fin d → Fv F v) :=
    fun x φ hφ => (hom' x.1 x.2 φ hφ).1
  have key : ∀ (g : UAtGrp σ X (evFin F v)) (h : UAtGrp σ W (evFin F v)) (φ : (Fin n × Fin d → Fv F v) → ℂ),
      φ ∈ SB (Fin n × Fin d → Fv F v) → ∀ φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
      Acts (evFin F v) (om (g.1, h.1)) φ φ₁ → φ₁ = om' (g, h) φ := fun g h φ hφ φ₁ _ hA =>
    GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr => (hA r hr).symm.trans ((hom' g h φ hφ).2 r hr)
  have haug : augAt om v = locAug om' := by
    apply le_antisymm
    · rw [augAt, Submodule.span_le]
      rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
      have e := key ⟨g, hg⟩ 1 φ hφ φ₁ hφ₁ hA
      exact Submodule.subset_span ⟨⟨g, hg⟩, φ, hφ, by rw [e]⟩
    · rw [locAug, Submodule.span_le]
      rintro z ⟨g, φ, hφ, rfl⟩
      exact Submodule.subset_span ⟨g.1, g.2, φ, hφ, om' (g, 1) φ, (hom' g 1 φ hφ).1, (hom' g 1 φ hφ).2, rfl⟩
  have hiff : ∀ P, ThetaSub om v P ↔ IsLocSub om' P := by
    intro P
    rw [ThetaSub, IsLocSub, haug]
    refine and_congr_right fun _ => and_congr_right fun hle => ⟨fun hs h φ hφ => ?_, fun hs h hh φ hφ φ₁ hφ₁ hA => ?_⟩
    · exact hs h.1 h.2 φ hφ _ (hom' 1 h φ (hle hφ)).1 (hom' 1 h φ (hle hφ)).2
    · rw [key 1 ⟨h, hh⟩ φ (hle hφ) φ₁ hφ₁ hA]
      exact hs _ φ hφ
  have hM : ∀ P, Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) P →
      Maximal (fun P => IsLocSub om' P ∧ P ≠ SB (Fin n × Fin d → Fv F v)) P := by
    intro P hP'
    simpa only [hiff] using hP'
  replace hN := hM N hN
  replace hN' := hM N' hN'
  have hsup : IsLocSub om' (N ⊔ N') := isLocSub_sup hN.1.1 hN'.1.1
  have hne : N ⊔ N' ≠ SB (Fin n × Fin d → Fv F v) :=
    GlobalTheory.HoweAdelic.sup_ne_SB_of_howeDuality om' hHDv hpres N N' hN.1.1 hN'.1.1 hN.1.2 hN'.1.2
  have h1 : N ⊔ N' ≤ N := hN.2 ⟨hsup, hne⟩ le_sup_left
  have h2 : N ⊔ N' ≤ N' := hN'.2 ⟨hsup, hne⟩ le_sup_right
  exact le_antisymm (le_sup_left.trans h2) (le_sup_right.trans h1)

end GlobalTheory.HoweNonsplit

end
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HoweAllPlaces

theorem eq_bot_of_subsingleton {D : Type} [Subsingleton D] (S P : Submodule ℂ (D → ℂ)) (hP : P ≤ S) (hne : P ≠ S) :
    P = ⊥ := by
  by_contra hb
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)
  apply hne
  refine le_antisymm hP fun y _ => ?_
  have : y = (y p / x p) • x := by
    funext q
    rw [Subsingleton.elim q p, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hp]
  rw [this]
  exact P.smul_mem _ hx

end GlobalTheory.HoweAllPlaces

open GlobalTheory.HoweAllPlaces in

theorem GlobalTheory.HoweAllPlaces.main : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.MinguezThetaGL → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, ∀ N N', Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N → Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N' → N = N' := by
  intro hP hHD hMin F E _ _ _ _ _ σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hweil v N N' hN hN'
  have key : ThetaSub om v (N ⊔ N') → N ⊔ N' ≠ SB _ → N = N' := by
    intro h1 h2
    have a := hN.2 ⟨h1, h2⟩ le_sup_left
    have b := hN'.2 ⟨h1, h2⟩ le_sup_right
    exact le_antisymm (le_sup_left.trans b) (le_sup_right.trans a)
  have hNS : N ≤ SB _ := hN.1.1.2.1
  have hNS' : N' ≤ SB _ := hN'.1.1.2.1
  rcases isEmpty_or_nonempty (E →ₐ[F] Fv F v) with hs | hs
  ·
    exact GlobalTheory.HoweNonsplit.unique_maximal hP hHD F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hweil v hs N N' hN hN'
  · rcases Nat.eq_zero_or_pos n with hn | hn
    ·
      subst hn
      rw [eq_bot_of_subsingleton _ N hNS hN.1.2, eq_bot_of_subsingleton _ N' hNS' hN'.1.2]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      rw [eq_bot_of_subsingleton _ N hNS hN.1.2, eq_bot_of_subsingleton _ N' hNS' hN'.1.2]

    obtain ⟨χ, ι, hχ, hbij, htr⟩ := GlobalTheory.SplitTransportPair.transport hP F E σ hcm n d X W M ψ χX χW om hψ hX hXd hW hWd hrX hrW hhX hhW hweil hn hd v hs
    have hsN := (htr N hNS).1 hN.1.1
    have hsN' := (htr N' hNS').1 hN'.1.1
    have h1 : ThetaSub om v (N ⊔ N') := (htr _ (sup_le hNS hNS')).2 (by rw [Submodule.map_sup]; exact hsN.sup hsN')
    have hSB : (SB (Fin n × Fin d → Fv F v)).map ι = GlobalTheory.SplitWeil.SB _ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hbij.mapsTo hx
      · intro hy
        obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
        exact ⟨x, hx, rfl⟩
    have hne : ∀ P : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ), P ≤ SB _ → P ≠ SB _ → P.map ι ≠ GlobalTheory.SplitWeil.SB _ := by
      intro P hP1 hP2 he
      apply hP2
      refine le_antisymm hP1 fun x hx => ?_
      have : ι x ∈ P.map ι := by rw [he, ← hSB]; exact Submodule.mem_map_of_mem hx
      obtain ⟨y, hy, hyx⟩ := this
      rwa [hbij.injOn (hP1 hy) hx hyx] at hy
    refine key h1 fun he => ?_
    apply GlobalTheory.ThetaGLSub.SumProper.main hP hMin _ n d hn hd χ hχ _ _ hsN hsN' (hne N hNS hN.1.2) (hne N' hNS' hN'.1.2)
    rw [← Submodule.map_sup, he, hSB]
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_cm_extension : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → GlobalTheory.Published.MinguezThetaGL → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, ∀ N N', Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N → Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N' → N = N' := by
  atlas_forward_decl GlobalTheory.HoweAllPlaces.main
end
