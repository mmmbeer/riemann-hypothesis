import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfK
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfA
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfAs

section
noncomputable section

open Formalism.L2.Theta Formalism.IndefR.Datum Matrix Filter Topology
open scoped ComplexOrder

namespace Formalism.IndefR.Tow.SobPf

section Gen

variable {n : ℕ}

theorem det_G_unit {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsUnit G.det := by
  rw [isUnit_iff_ne_zero]
  have h1 := hs.2.2.det_pos.ne'
  rw [Matrix.det_mul] at h1
  exact left_ne_zero_of_mul h1

theorem det_UH_unit {G g : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    IsUnit g.det := by
  have h : gᴴ * G * g = G := hg
  have h' := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h'
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h'
  exact hG.ne_zero h'.symm

theorem inv_mem_UH {G g : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G) :
    g⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have hd := det_UH_unit hG hg
  have h : gᴴ * G * g = G := hg
  show (g⁻¹)ᴴ * G * g⁻¹ = G
  calc (g⁻¹)ᴴ * G * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * G * g) * g⁻¹ := by rw [h]
    _ = (g * g⁻¹)ᴴ * G * (g * g⁻¹) := by rw [Matrix.conjTranspose_mul]; simp only [mul_assoc]
    _ = G := by rw [Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one, one_mul, mul_one]

theorem conj_mem_lieG {G g X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (hX : X ∈ lieG G) : g⁻¹ * X * g ∈ lieG G := by
  have hd := det_UH_unit hG hg
  have h : gᴴ * G * g = G := hg
  have hX' : Xᴴ * G + G * X = 0 := hX
  have e0 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hd
  have e1 : G * g⁻¹ = gᴴ * G := by
    calc G * g⁻¹ = gᴴ * G * g * g⁻¹ := by rw [h]
      _ = gᴴ * G := by rw [Matrix.mul_assoc, e0, Matrix.mul_one]
  have e2 : (g⁻¹)ᴴ * G = G * g := by
    calc (g⁻¹)ᴴ * G = (g⁻¹)ᴴ * (gᴴ * G * g) := by rw [h]
      _ = (g * g⁻¹)ᴴ * G * g := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G * g := by rw [e0, Matrix.conjTranspose_one, Matrix.one_mul]
  show (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = gᴴ * Xᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * X * g := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * G + G * X) * g := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem deriv_clm_inv (A B : H →L[ℂ] H) (hBA : ∀ v, B (A v) = v) (f : ℝ → H) :
    deriv (fun t => A (f t)) 0 = A (deriv f 0) := by
  by_cases hf : DifferentiableAt ℝ f 0
  · exact ((A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hf.hasDerivAt).deriv
  · have hAf : ¬ DifferentiableAt ℝ (fun t => A (f t)) 0 := by
      intro h
      apply hf
      have e : (fun t => B (A (f t))) = f := funext fun t => hBA (f t)
      rw [← e]
      exact (B.restrictScalars ℝ).differentiableAt.comp 0 h
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hAf, map_zero]

theorem dRep_rep {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) (hG : IsUnit G.det) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (u : H) :
    dRep π X (π g u) = π g (dRep π (g⁻¹ * X * g) u) := by
  have hd := det_UH_unit hG hg
  have hY := conj_mem_lieG hG hg hX
  have hfun : (fun t : ℝ => π (NormedSpace.exp (t • X)) (π g u)) =
      fun t : ℝ => π g (π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) := by
    funext t
    have he : NormedSpace.exp (t • X) * g = g * NormedSpace.exp (t • (g⁻¹ * X * g)) := by
      rw [← Matrix.smul_mul, ← Matrix.mul_smul,
        Matrix.exp_conj' g (t • X) ((Matrix.isUnit_iff_isUnit_det _).2 hd)]
      simp only [← mul_assoc, Matrix.mul_nonsing_inv _ hd, one_mul]
    calc π (NormedSpace.exp (t • X)) (π g u) = π (NormedSpace.exp (t • X) * g) u := by
          rw [hπ.2.1 _ (expS_mem_UH hX t) _ hg]; rfl
      _ = π (g * NormedSpace.exp (t • (g⁻¹ * X * g))) u := by rw [he]
      _ = π g (π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) := by
          rw [hπ.2.1 _ hg _ (expS_mem_UH hY t)]; rfl
  have hBA : ∀ v, π g⁻¹ (π g v) = v := by
    intro v
    rw [← ContinuousLinearMap.comp_apply, ← hπ.2.1 _ (inv_mem_UH hG hg) _ hg, Matrix.nonsing_inv_mul _ hd, hπ.1]
    rfl
  show deriv (fun t : ℝ => π (NormedSpace.exp (t • X)) (π g u)) 0 =
    π g (deriv (fun t : ℝ => π (NormedSpace.exp (t • (g⁻¹ * X * g))) u) 0)
  rw [hfun]
  exact deriv_clm_inv (π g) (π g⁻¹) hBA _

theorem dL_rep {G : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) (hG : IsUnit G.det) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH G)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ lieG G) (u : H) :
    dL π l (π g u) = π g (dL π (l.map fun X => g⁻¹ * X * g) u) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    show dRep π X (dL π l (π g u)) = π g (dRep π (g⁻¹ * X * g) (dL π (l.map fun X => g⁻¹ * X * g) u))
    rw [ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)), dRep_rep hπ hG hg (hl X (by simp)) _]

end Gen

theorem foldBddK_of (h4 : SobChart) : FoldBddK := by
  intro n H _ _ G s π hs hπ w hw l hl
  have hG := det_G_unit hs
  have hc1 : Cont1 := continuity_of_sobolev_chart h4 foldCont_holds
  have hcont : ContinuousOn (fun k : Fin n → Fin n → ℂ => dL π l (π (Matrix.of k) w))
      {k | Matrix.of k ∈ KAt G s} := by
    intro k0 hk0
    have hk0K : Matrix.of k0 ∈ KAt G s := hk0
    have hk0U : Matrix.of k0 ∈ Formalism.QuantumDeterminants.UH G := hk0K.1
    have hd := det_UH_unit hG hk0U
    have hl' : ∀ X ∈ l.map (fun X => (Matrix.of k0)⁻¹ * X * Matrix.of k0), X ∈ lieG G := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact conj_mem_lieG hG hk0U (hl Y hY)
    refine Metric.continuousWithinAt_iff.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hδ'⟩ := hc1 G s π hs hπ w hw _ hl' ε hε
    have hO : IsOpen {k : Fin n → Fin n → ℂ |
        ∀ i j, ‖((Matrix.of k0)⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ} := by
      have hc : ∀ i j, Continuous fun k : Fin n → Fin n → ℂ =>
          ‖((Matrix.of k0)⁻¹ * Matrix.of k) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ := fun i j =>
        (((continuous_const.matrix_mul
          (continuous_id' : Continuous fun k : Fin n → Fin n → ℂ => Matrix.of k)).matrix_elem i j).sub
            continuous_const).norm
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt (hc i j) continuous_const
    have hk0O : ∀ i j, ‖((Matrix.of k0)⁻¹ * Matrix.of k0) i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ < δ := by
      intro i j
      rw [Matrix.nonsing_inv_mul _ hd, sub_self, norm_zero]
      exact hδ
    obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.1 hO k0 hk0O
    refine ⟨ρ, hρ, fun {k} hk hdk => ?_⟩
    have hkK : Matrix.of k ∈ KAt G s := hk
    have hkU : Matrix.of k ∈ Formalism.QuantumDeterminants.UH G := hkK.1
    have hg : (Matrix.of k0)⁻¹ * Matrix.of k ∈ Formalism.QuantumDeterminants.UH G := mul_mem_UH₂ G _ (inv_mem_UH hG hk0U) _ hkU
    have hnear := hρO (Metric.mem_ball.2 hdk)
    have hkk : π (Matrix.of k) w = π (Matrix.of k0) (π ((Matrix.of k0)⁻¹ * Matrix.of k) w) := by
      rw [← ContinuousLinearMap.comp_apply, ← hπ.2.1 _ hk0U _ hg, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
    rw [dist_eq_norm]
    rw [hkk, dL_rep hπ hG hk0U l hl, dL_rep hπ hG hk0U l hl, ← map_sub, hπ.2.2.1 _ hk0U]
    exact hδ' _ hg hnear
  have hK : IsCompact {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isCompact_KAt hs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  exact ⟨C, fun k hk => hC (Matrix.of.symm k) hk⟩

end Formalism.IndefR.Tow.SobPf

end
end

section
noncomputable section

open Formalism.IndefR.Datum Matrix MeasureTheory Topology

namespace Formalism.IndefR.Tow.SobPf

variable {n : ℕ}

theorem mul_mem_KAt {G s a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KAt G s) (hb : b ∈ KAt G s) :
    a * b ∈ KAt G s := by
  have ha' : a ∈ Formalism.QuantumDeterminants.UH G ∧ a * s = s * a := ha
  have hb' : b ∈ Formalism.QuantumDeterminants.UH G ∧ b * s = s * b := hb
  have h1 : aᴴ * G * a = G := ha'.1
  have h2 : bᴴ * G * b = G := hb'.1
  show a * b ∈ Formalism.QuantumDeterminants.UH G ∧ a * b * s = s * (a * b)
  refine ⟨?_, ?_⟩
  · show (a * b)ᴴ * G * (a * b) = G
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * G * (a * b) = bᴴ * (aᴴ * G * a) * b := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]
  · calc a * b * s = a * (b * s) := Matrix.mul_assoc _ _ _
      _ = a * (s * b) := by rw [hb'.2]
      _ = (a * s) * b := (Matrix.mul_assoc _ _ _).symm
      _ = (s * a) * b := by rw [ha'.2]
      _ = s * (a * b) := Matrix.mul_assoc _ _ _

theorem inv_mem_KAt {G s a : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (ha : a ∈ KAt G s) :
    a⁻¹ ∈ KAt G s := by

  have ha' : a ∈ Formalism.QuantumDeterminants.UH G ∧ a * s = s * a := ha
  have h1 : aᴴ * G * a = G := ha'.1
  have hleft : (G⁻¹ * aᴴ * G) * a = 1 := by
    calc (G⁻¹ * aᴴ * G) * a = G⁻¹ * (aᴴ * G * a) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hG]
  have hdet : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hleft
  have hright : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hdet
  have hleft' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hdet
  show a⁻¹ ∈ Formalism.QuantumDeterminants.UH G ∧ a⁻¹ * s = s * a⁻¹
  refine ⟨?_, ?_⟩
  · show (a⁻¹)ᴴ * G * a⁻¹ = G
    calc (a⁻¹)ᴴ * G * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * G * a) * a⁻¹ := by rw [h1]
      _ = (a * a⁻¹)ᴴ * G * (a * a⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hright]; simp
  · calc a⁻¹ * s = a⁻¹ * s * (a * a⁻¹) := by rw [hright, Matrix.mul_one]
      _ = a⁻¹ * (s * a) * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = a⁻¹ * (a * s) * a⁻¹ := by rw [ha'.2]
      _ = (a⁻¹ * a) * s * a⁻¹ := by simp only [Matrix.mul_assoc]
      _ = s * a⁻¹ := by rw [hleft', Matrix.one_mul]


def Kg {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s}
  mul_mem' {a b} ha hb := by
    show ((a * b : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Units.val_mul]; exact mul_mem_KAt ha hb
  one_mem' := by
    show ((1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Units.val_one]; exact one_mem_KAt G s
  inv_mem' {a} ha := by
    show ((a⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
    rw [Matrix.coe_units_inv]; exact inv_mem_KAt (det_G_unit hs) ha

theorem isCompact_Kg {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) :
    IsCompact ((Kg hs : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ) : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) := by

  have hGu : IsUnit G.det := det_G_unit hs
  haveI : CompactSpace (KAt G s) := isCompact_iff_compactSpace.mp (isCompact_KAt hs)
  have hl : ∀ k ∈ KAt G s, (G⁻¹ * kᴴ * G) * k = 1 := fun k hk => by
    have h1 : kᴴ * G * k = G := (show k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k from hk).1
    calc (G⁻¹ * kᴴ * G) * k = G⁻¹ * (kᴴ * G * k) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hGu]
  have hr : ∀ k ∈ KAt G s, k * (G⁻¹ * kᴴ * G) = 1 := fun k hk => by
    rw [← Matrix.inv_eq_left_inv (hl k hk)]
    exact Matrix.mul_nonsing_inv k (Matrix.isUnit_det_of_left_inverse (hl k hk))
  let F : KAt G s → (Matrix (Fin n) (Fin n) ℂ)ˣ := fun k =>
    ⟨k.1, G⁻¹ * k.1ᴴ * G, hr k.1 k.2, hl k.1 k.2⟩
  have hF : Continuous F := by
    rw [Units.continuous_iff]
    refine ⟨continuous_subtype_val, ?_⟩
    exact (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul
      continuous_const
  have he : ((Kg hs : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ) : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) =
      Set.range F := by
    ext u
    constructor
    · intro hu
      exact ⟨⟨u.1, hu⟩, Units.ext rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  rw [he]
  exact isCompact_range hF

private theorem exists_Kg_coe_eq_of_mem_KAt {G s k : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) (hk : k ∈ KAt G s) :
    ∃ u : Kg hs, ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k := by
  have hGu : IsUnit G.det := det_G_unit hs
  have h1 : kᴴ * G * k = G := (show k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k from hk).1
  have hleft : (G⁻¹ * kᴴ * G) * k = 1 := by
    calc (G⁻¹ * kᴴ * G) * k = G⁻¹ * (kᴴ * G * k) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.nonsing_inv_mul G hGu]
  have hdet : IsUnit k.det := Matrix.isUnit_det_of_left_inverse hleft
  exact ⟨⟨⟨k, k⁻¹, Matrix.mul_nonsing_inv k hdet, Matrix.nonsing_inv_mul k hdet⟩, hk⟩, rfl⟩

theorem haarExists_holds : HaarExists := by
  intro n G s hs
  haveI : CompactSpace (Kg hs) := isCompact_iff_compactSpace.mp (isCompact_Kg hs)
  letI : MeasurableSpace (Kg hs) := borel (Kg hs)
  haveI : BorelSpace (Kg hs) := ⟨rfl⟩
  let ν : Measure (Kg hs) := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    have h := Measure.haarMeasure_self (G := Kg hs) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h
  let φ : Kg hs → (Fin n → Fin n → ℂ) := fun u =>
    Matrix.of.symm ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  have hφ : Continuous φ := by
    show Continuous (fun u : Kg hs => ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
    exact Units.continuous_val.comp continuous_subtype_val
  have hφm : Measurable φ := hφ.measurable
  have hcl : IsClosed {k : Fin n → Fin n → ℂ | Matrix.of k ∈ KAt G s} := isClosed_KAt G s
  refine ⟨ν.map φ, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [Measure.map_apply hφm MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ
  · rw [ae_map_iff hφm.aemeasurable hcl.measurableSet]
    exact ae_of_all _ fun u => by
      show ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ KAt G s
      exact u.2
  · intro k₀ hk₀
    obtain ⟨u₀, hu₀⟩ := exists_Kg_coe_eq_of_mem_KAt hs hk₀
    have hT : Continuous (fun k : Fin n → Fin n → ℂ => Matrix.of.symm (k₀ * Matrix.of k)) := by
      show Continuous (fun k : Matrix (Fin n) (Fin n) ℂ => k₀ * k)
      exact continuous_const.matrix_mul continuous_id
    have hL : Measurable (fun u : Kg hs => u₀ * u) := (continuous_const.mul continuous_id).measurable
    have hcomp : (fun k : Fin n → Fin n → ℂ => Matrix.of.symm (k₀ * Matrix.of k)) ∘ φ =
        φ ∘ (fun u : Kg hs => u₀ * u) := by
      funext u
      show Matrix.of.symm (k₀ * ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
        Matrix.of.symm (((u₀ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
          ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
      rw [hu₀]
    rw [Measure.map_map hT.measurable hφm, hcomp, ← Measure.map_map hφm hL,
      map_mul_left_eq_self]
  · rintro U hU ⟨k, hkU, hkK⟩
    obtain ⟨u, hu⟩ := exists_Kg_coe_eq_of_mem_KAt hs hkK
    rw [Measure.map_apply hφm hU.measurableSet]
    refine (hU.preimage hφ).measure_pos ν ⟨u, ?_⟩
    show Matrix.of.symm ((u : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ U
    rw [hu]
    exact hkU

end Formalism.IndefR.Tow.SobPf

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace KFin

variable {n : ℕ}

def KS (G s : Matrix (Fin n) (Fin n) ℂ) : Set (Fin n → Fin n → ℂ) := {k | Matrix.of k ∈ KAt G s}

theorem isCompact_KS {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCompact (KS G s) := isCompact_KAt hs


section Int

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuousOn_avg {G s : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) {p : (Fin n → Fin n → ℂ) → ℂ} (hp : Continuous p) (w : H) :
    ContinuousOn (fun k => p k • π (Matrix.of k) w) (KS G s) := by

  have hmaps : Set.MapsTo (fun k : Fin n → Fin n → ℂ => Matrix.of k) (KS G s) (Formalism.QuantumDeterminants.UH G) :=
    fun k hk => (show Matrix.of k ∈ Formalism.QuantumDeterminants.UH G ∧ Matrix.of k * s = s * Matrix.of k from hk).1
  have hof : ContinuousOn (fun k : Fin n → Fin n → ℂ => Matrix.of k) (KS G s) :=
    continuous_id.continuousOn
  have h1 : ContinuousOn (fun k : Fin n → Fin n → ℂ => π (Matrix.of k) w) (KS G s) :=
    (hπ.2.2.2 w).comp hof hmaps
  exact hp.continuousOn.smul h1

theorem integrable_avg {G s : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hs : IsCartanInv G s) (hπ : IsGRep G π) {μ : Measure (Fin n → Fin n → ℂ)} (hμ : IsHaarK G s μ)
    {p : (Fin n → Fin n → ℂ) → ℂ} (hp : Continuous p) (w : H) :
    Integrable (fun k => p k • π (Matrix.of k) w) μ := by

  haveI := hμ.1
  have hae : ∀ᵐ k ∂μ, k ∈ KS G s := hμ.2.1
  have h := (continuousOn_avg (s := s) hπ hp w).integrableOn_compact (μ := μ) (isCompact_KS hs)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h

end Int

abbrev Var (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

def subst (A : Matrix (Fin n) (Fin n) ℂ) : Var n → MvPolynomial (Var n) ℂ
  | Sum.inl ij => ∑ l, MvPolynomial.C (A ij.1 l) * MvPolynomial.X (Sum.inl (l, ij.2))
  | Sum.inr ij => ∑ l, MvPolynomial.C (starRingEnd ℂ (A ij.1 l)) * MvPolynomial.X (Sum.inr (l, ij.2))

theorem evalMatrix_bind₁_mulLeft (A : Matrix (Fin n) (Fin n) ℂ) (q : MvPolynomial (Var n) ℂ) (k : Fin n → Fin n → ℂ) :
    evP (MvPolynomial.bind₁ (subst A) q) k = evP q (Matrix.of.symm (A * Matrix.of k)) := by

  induction q using MvPolynomial.induction_on
  next a =>
    simp [evP]
  next p r hp hr =>
    simp only [evP, map_add] at hp hr ⊢
    rw [hp, hr]
  next p v hp =>
    simp only [evP, map_mul, MvPolynomial.bind₁_X_right, MvPolynomial.eval_X] at hp ⊢
    rw [hp]
    congr 1
    rcases v with ⟨i, j⟩ | ⟨i, j⟩
    · simp [subst, Matrix.mul_apply, Matrix.of_apply, MvPolynomial.eval_X, MvPolynomial.eval_C]
    · simp [subst, Matrix.mul_apply, Matrix.of_apply, MvPolynomial.eval_X, MvPolynomial.eval_C, map_sum]

theorem totalDegree_subst (A : Matrix (Fin n) (Fin n) ℂ) (v : Var n) : (subst A v).totalDegree ≤ 1 := by

  rcases v with ij | ij <;>
  · simp only [subst]
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp

theorem totalDegree_bind_le (A : Matrix (Fin n) (Fin n) ℂ) (q : MvPolynomial (Var n) ℂ) :
    (MvPolynomial.bind₁ (subst A) q).totalDegree ≤ q.totalDegree := by

  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finset_prod _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul le_rfl (totalDegree_subst A i))) ?_
  simp only [mul_one]
  exact MvPolynomial.le_totalDegree hm

def Mon (n N : ℕ) : Set (Var n →₀ ℕ) := {m | (m.sum fun _ e => e) ≤ N}

theorem finite_Mon (n N : ℕ) : (Mon n N).Finite := by

  refine (Set.finite_range (fun f : Var n → Fin (N + 1) =>
    Finsupp.equivFunOnFinite.symm (fun v => (f v : ℕ)))).subset ?_
  intro m hm
  have hm' : ∑ v ∈ m.support, m v ≤ N := hm
  have hle : ∀ v, m v ≤ N := by
    intro v
    by_cases hv : v ∈ m.support
    · exact le_trans (Finset.single_le_sum (f := fun v => m v) (fun _ _ => Nat.zero_le _) hv) hm'
    · have h0 : m v = 0 := by simpa using hv
      rw [h0]; exact Nat.zero_le _
  refine ⟨fun v => ⟨m v, Nat.lt_succ_of_le (hle v)⟩, ?_⟩
  ext v
  simp

theorem evalMatrix_eq_sum_monomial (q : MvPolynomial (Var n) ℂ) (k : Fin n → Fin n → ℂ) :
    evP q k = ∑ m ∈ q.support, q.coeff m * evP (MvPolynomial.monomial m 1) k := by

  simp only [evP]
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show MvPolynomial.monomial m (q.coeff m) =
      MvPolynomial.C (q.coeff m) * MvPolynomial.monomial m (1 : ℂ) by
    rw [MvPolynomial.C_mul_monomial, mul_one], map_mul, MvPolynomial.eval_C]

end KFin

end Formalism.IndefR.Tow.SobPf

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace KFin

theorem avgKFin_holds : AvgKFin := by
  intro n H _ _ _ G s π hs hπ μ hμ q w
  classical
  have := hμ.1
  set N := q.totalDegree with hN
  let e : (Var n →₀ ℕ) → H := fun m => ∫ k, evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w ∂μ
  let W : Submodule ℂ H := Submodule.span ℂ (e '' Mon n N)
  have hfin : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ ((finite_Mon n N).image e)
  have hmemW : ∀ q' : MvPolynomial (Var n) ℂ, q'.totalDegree ≤ N →
      (∫ k, evP q' k • π (Matrix.of k) w ∂μ) ∈ W := by
    intro q' hq'
    have hint : ∀ m : Var n →₀ ℕ,
        Integrable (fun k => evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w) μ :=
      fun m => integrable_avg hs hπ hμ (continuous_evP _) w
    have e1 : (fun k => evP q' k • π (Matrix.of k) w) = fun k => ∑ m ∈ q'.support,
        q'.coeff m • (evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w) := by
      funext k
      rw [evalMatrix_eq_sum_monomial q' k, Finset.sum_smul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_smul]
    have hint' : ∀ m ∈ q'.support, Integrable
        (fun k => q'.coeff m • (evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w)) μ :=
      fun m _ => (hint m).smul (q'.coeff m)
    rw [e1, integral_finset_sum _ hint']
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [integral_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, ?_, rfl⟩)
    exact (MvPolynomial.le_totalDegree hm).trans hq'
  refine ⟨W, hfin, hmemW q le_rfl, ?_⟩
  intro k₀ hk₀ x hx
  have hG := det_G_unit hs
  have hk₀d := det_UH_unit hG hk₀.1
  have key : ∀ q' : MvPolynomial (Var n) ℂ, π k₀ (∫ k, evP q' k • π (Matrix.of k) w ∂μ) =
      ∫ k, evP (MvPolynomial.bind₁ (subst k₀⁻¹) q') k • π (Matrix.of k) w ∂μ := by
    intro q'
    rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hs hπ hμ (continuous_evP _) w)]
    have hT : Continuous fun k : Fin n → Fin n → ℂ => Matrix.of.symm (k₀ * Matrix.of k) :=
      (continuous_const.matrix_mul continuous_id : Continuous fun k : Matrix (Fin n) (Fin n) ℂ => k₀ * k)
    let F : (Fin n → Fin n → ℂ) → H := fun k' =>
      evP (MvPolynomial.bind₁ (subst k₀⁻¹) q') k' • π (Matrix.of k') w
    have hFm : AEStronglyMeasurable F (μ.map fun k => Matrix.of.symm (k₀ * Matrix.of k)) := by
      rw [hμ.2.2.1 k₀ hk₀]; exact (integrable_avg hs hπ hμ (continuous_evP _) w).1
    have h1 : ∫ k', F k' ∂μ = ∫ k, F (Matrix.of.symm (k₀ * Matrix.of k)) ∂μ := by
      conv_lhs => rw [← hμ.2.2.1 k₀ hk₀]
      exact integral_map hT.aemeasurable hFm
    show _ = ∫ k', F k' ∂μ
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [hμ.2.1] with k hk
    simp only [F]
    rw [evalMatrix_bind₁_mulLeft, Equiv.apply_symm_apply, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hk₀d, Matrix.one_mul,
      Equiv.symm_apply_apply, hπ.2.1 _ hk₀.1 _ hk.1, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.map_smul]
  have hstep : ∀ m ∈ Mon n N, π k₀ (e m) ∈ W := by
    intro m hm
    show π k₀ (∫ k, evP (MvPolynomial.monomial m 1) k • π (Matrix.of k) w ∂μ) ∈ W
    rw [key]
    refine hmemW _ ((totalDegree_bind_le _ _).trans ?_)
    rw [MvPolynomial.totalDegree_monomial m one_ne_zero]
    exact hm
  have hle : W ≤ W.comap (π k₀ : H →ₗ[ℂ] H) := by
    show Submodule.span ℂ (e '' Mon n N) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    exact hstep m hm
  exact hle hx

end KFin

theorem avgKFin_holds : AvgKFin := KFin.avgKFin_holds

end Formalism.IndefR.Tow.SobPf

end
end
