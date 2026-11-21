import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG GlobalTheory.GLDoubling
open scoped NNReal Pointwise

namespace GlobalTheory.GLDoubling.Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_haar (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] :
    ∃ μ : Measure (GL (Fin n) k), μ.IsHaarMeasure ∧ μ (KO k (Fin n)) = 1 := by
  have ho : IsOpen (KO k (Fin n) : Set (GL (Fin n) k)) := SplitFlip.isOpen_KO
  have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := SplitFlip.isCompact_KO
  let K : TopologicalSpace.PositiveCompacts (GL (Fin n) k) := ⟨⟨_, hc⟩, by
    rw [show interior ((⟨_, hc⟩ : TopologicalSpace.Compacts (GL (Fin n) k)).carrier) = _ from ho.interior_eq]
    exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem act_one {π : Representation ℂ (GL (Fin 1) k) V} {a : Fin 1 → ℂˣ} (ha : HasSatake π a) (y : kˣ) (v : V) :
    π (diagT k (Fin 1) fun _ => y) v = (unrChar k (a 0) y : ℂ) • v := by
  refine GlobalTheory.SmGL.Model.scalar_of_isSubquotient ha.2.2 (fun f => ?_) v
  ext x
  have h1 := parInd_law (points (Fin 1)) _ f ⟨_, leviEmb_mem_parab k _ (leviTorus k _ fun _ => y)⟩ x
  rw [leviProj_leviEmb] at h1
  have hc : x * (diagT k (Fin 1) fun _ => y) = (diagT k (Fin 1) fun _ => y) * x := by
    ext i j
    simp [Matrix.mul_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0]
  show f.1.1 (x * (diagT k (Fin 1) fun _ => y)) = (unrChar k (a 0) y : ℂ) • f.1.1 x
  rw [hc]
  refine h1.trans ?_
  have hm : modExp (fun _ : Fin 1 => Unit) 0 = 0 := by rw [modExp_fin _ (fun _ => by simp)]; simp
  simp [deltaHalf_apply, hm]

theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; simp at hx; exact uniformizer_ne_zero hx.symm), hx⟩

theorem rank_zero [MeasurableSpace (GL (Fin 0) k)] [BorelSpace (GL (Fin 0) k)]
    (μ : Measure (GL (Fin 0) k)) [μ.IsHaarMeasure] (hμ : μ (KO k (Fin 0)) = 1)
    (π : Representation ℂ (GL (Fin 0) k) V) (α : Fin 0 → ℂˣ)
    (ω : GL (Fin 0) k → ℂ) (hω : IsZonal π (KO k (Fin 0)) ω) (s : ℂ) :
      Integrable (fun g => sphSection k (Fin 0) s (io k (Fin 0) (g, 1)) * ω g) μ ∧
      ∫ g, sphSection k (Fin 0) s (io k (Fin 0) (g, 1)) * ω g ∂μ =
        lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) *
          invNormFactor (resCard k) 0 s := by
  have hs : ∀ g : GL (Fin 0) k, g = 1 := fun g => by ext i; exact i.elim0
  have hu : (KO k (Fin 0) : Set (GL (Fin 0) k)) = Set.univ :=
    Set.eq_univ_of_forall fun g => by rw [hs g]; exact one_mem _
  rw [hu] at hμ
  haveI : IsProbabilityMeasure μ := ⟨hμ⟩
  obtain ⟨v, -, l, -, hl, hω⟩ := hω
  have : (fun g => sphSection k (Fin 0) s (io k (Fin 0) (g, 1)) * ω g) = fun _ => 1 := funext fun g => by
    rw [hs g, hω, show ((1 : GL (Fin 0) k), (1 : GL (Fin 0) k)) = 1 from rfl, map_one, sphSection_one]
    simpa using hl
  rw [this]
  simp [lFactor, invNormFactor]

end GlobalTheory.GLDoubling.Model
