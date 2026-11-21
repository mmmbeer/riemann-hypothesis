import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicReductionImage
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocIdxLift

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def OEp (p : TypX X) : Set (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :=
  PI.FinKW.psiV X.B.I p.1 '' (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E : Set _)

def InModP (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    (y : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) : Prop :=
  y ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s} ⊔
    Ideal.span {((m : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def LocCong (p : TypX X) (y : HAp X p) : Prop :=
  (∀ a : Fin D.R.rS, InModP X p X.B.g ((fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) '' {b | b.1 < a.1})
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J y :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 (X.e0 a))) ∧
  InModP X p X.B.g (Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b))
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J y :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 X.z0) ∧
  ∀ i : Fin D.R.k, InModP X p X.B.g ((Set.range fun b => PI.FinKW.vecV X.B.I p.1 (X.e0 b)) ∪
      (fun j => PI.FinKW.vecV X.B.I p.1 (X.bw j)) '' {j | j.1 < i.1})
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J y :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 (X.bw i))

def StImAloc (p : TypX X) : Prop := KppX X hb p = {y | y ∈ KvX X p ∧ LocCong X p y}

end Loc

end MassDataIdxSteps
end
end

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem imA_vecV_smul (p : TypX X) (t : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 (t • w) = PI.FinKW.psiV X.B.I p.1 t • PI.FinKW.vecV X.B.I p.1 w := by
  funext i; simp [PI.FinKW.vecV, map_mul]

theorem imA_vecV_add (p : TypX X) (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 (a + b) = PI.FinKW.vecV X.B.I p.1 a + PI.FinKW.vecV X.B.I p.1 b := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_vecV_zero (p : TypX X) :
    PI.FinKW.vecV X.B.I p.1 (0 : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) = 0 := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_OEp_mul (p : TypX X) {s t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (hs : s ∈ OEp X p)
    (ht : t ∈ OEp X p) : s * t ∈ OEp X p := by
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb', rfl⟩ := ht
  exact ⟨a * b, Subring.mul_mem _ ha hb', map_mul _ _ _⟩

theorem smul_mem_spanAt (p : TypX X) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    {t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (ht : t ∈ OEp X p)
    {w : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hw : w ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s}) :
    t • w ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F) {w | ∃ t ∈ OEp X p, ∃ s ∈ S, w = t • s} := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t', ht', s, hs, rfl⟩ := hx
    exact Submodule.subset_span ⟨t * t', imA_OEp_mul X p ht ht', s, hs, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ c hx

theorem imA_inMod_loc (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (h : InMod X.B.I m S w) :
    InModP X p m (PI.FinKW.vecV X.B.I p.1 '' S) (PI.FinKW.vecV X.B.I p.1 w) := by
  obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp h
  clear h
  rw [imA_vecV_add]
  refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, rfl⟩
  · induction ha using Submodule.span_induction with
    | mem x hx =>
      exact Submodule.subset_span ⟨1, ⟨1, one_mem _, map_one _⟩, _, ⟨x, hx, rfl⟩, (one_smul _ _).symm⟩
    | zero => rw [imA_vecV_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [imA_vecV_add]; exact add_mem hx hy
    | smul c x _ hx =>
      show PI.FinKW.vecV X.B.I p.1 ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • x) ∈ _
      rw [imA_vecV_smul]
      exact smul_mem_spanAt X p _ ⟨c, c.2, rfl⟩ hx
  · have key : ∃ x ∈ X.B.I.Lf, b = (m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • x := by
      induction hb' using Submodule.span_induction with
      | mem y hy => exact hy
      | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
      | add y z _ _ hy hz =>
        obtain ⟨y', hy', rfl⟩ := hy
        obtain ⟨z', hz', rfl⟩ := hz
        exact ⟨y' + z', add_mem hy' hz', (smul_add _ _ _).symm⟩
      | smul c y _ hy =>
        obtain ⟨y', hy', rfl⟩ := hy
        refine ⟨c • y', Submodule.smul_mem _ c hy', ?_⟩
        show (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • _ = _ • ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • y')
        rw [smul_smul, smul_smul, mul_comm]
    obtain ⟨x, hx, rfl⟩ := key
    rw [imA_vecV_smul, map_natCast, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (p.1.adicCompletionIntegers X.B.I.F)]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I x hx p.1)

theorem imA_vecV_mulVec (p : TypX X) (x : X.B.I.Gf)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I p.1 ((X.B.I.fmat x - 1) *ᵥ w) =
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (piV X.B.I p.1 (tf X.B.I hb x)) :
        GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 w := by
  rw [LocIdxLift_vecV_mulVec, Matrix.map_sub _ (map_sub _), LocIdxLift_psiV_fmat X.B.I hb,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem imA_kpp_sub (p : TypX X) : KppX X hb p ⊆ {y | y ∈ KvX X p ∧ LocCong X p y} := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hx' : x ∈ X.B.I.Kset ∧ K2cong X.B.I X.B.g X.e0 X.z0 X.bw x := hx
  obtain ⟨hxK, h1, h2, h3⟩ := hx'
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hK := (Bridge_mem_Kf_iff X.B.I hb x).mpr hxK
    rw [Kf, Subgroup.mem_iInf] at hK
    exact hK p.1
  · intro a
    have h := imA_inMod_loc X p _ _ _ (h1 a)
    rw [imA_vecV_mulVec X hb, Set.image_image] at h
    exact h
  · have h := imA_inMod_loc X p _ _ _ h2
    rw [imA_vecV_mulVec X hb, ← Set.range_comp] at h
    exact h
  · intro i
    have h := imA_inMod_loc X p _ _ _ (h3 i)
    rw [imA_vecV_mulVec X hb, Set.image_union, Set.image_image, ← Set.range_comp] at h
    exact h

end MassDataIdxSteps
end
end

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def scP (p : TypX X) (c : Fv X.B.I.F p.1) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F :=
  eOf X.B.I (singleV X.B.I.F p.1 c)

theorem imA_psiV_eOf (v : HeightOneSpectrum (𝓞 X.B.I.F)) (a : Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.psiV X.B.I v (eOf X.B.I a) = algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (a v) := by
  simp [PI.FinKW.psiV, eOf]
  rfl

theorem component_scalarAt_same (p : TypX X) (c : Fv X.B.I.F p.1) :
    PI.FinKW.psiV X.B.I p.1 (scP X p c) = algebraMap (Fv X.B.I.F p.1) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) c := by
  rw [scP, imA_psiV_eOf, Comp_single_same]

theorem component_scalarAt_of_ne (p : TypX X) (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h : v ≠ p.1)
    (c : Fv X.B.I.F p.1) : PI.FinKW.psiV X.B.I v (scP X p c) = 0 := by
  rw [scP, imA_psiV_eOf, Comp_single_ne X.B.I p.1 v h, map_zero]

theorem scalarAt_mem_integralAdeles (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F) :
    scP X p (c : Fv X.B.I.F p.1) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  apply LocB_eOf_mem
  intro v
  by_cases h : v = p.1
  · subst h; show singleV X.B.I.F _ _ _ ∈ _; rw [Comp_single_same]; exact c.2
  · show singleV X.B.I.F p.1 _ v ∈ _; rw [Comp_single_ne X.B.I p.1 v h]; exact zero_mem _

theorem imA_smul_alg (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F)
    (u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :
    c • u = algebraMap (Fv X.B.I.F p.1) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) (c : Fv X.B.I.F p.1) • u := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Algebra.smul_def]
  rfl

theorem imA_vecV_sub (v : HeightOneSpectrum (𝓞 X.B.I.F)) (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a - b) = PI.FinKW.vecV X.B.I v a - PI.FinKW.vecV X.B.I v b := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_vecV_smul' (v : HeightOneSpectrum (𝓞 X.B.I.F)) (t : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (t • w) = PI.FinKW.psiV X.B.I v t • PI.FinKW.vecV X.B.I v w := by
  funext i; simp [PI.FinKW.vecV, map_mul]

theorem imA_vec_ext (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (h : ∀ v, PI.FinKW.vecV X.B.I v w = 0) : w = 0 := by
  funext i
  exact PI.FinKW.local_vector_injective X.B.I (w i) fun v => congrFun (h v) i

end MassDataIdxSteps
end
end

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

theorem imA_vecV_add' (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a + b) = PI.FinKW.vecV X.B.I v a + PI.FinKW.vecV X.B.I v b := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_vecV_zero' (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    PI.FinKW.vecV X.B.I v (0 : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) = 0 := by
  funext i; simp [PI.FinKW.vecV]

theorem scalarAt_one_mem_integralAdeles (p : TypX X) : scP X p 1 ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  have h := scalarAt_mem_integralAdeles X p 1
  simpa using h

theorem imA_lift_sp (p : TypX X) (S : Set (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
    {a : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (ha : a ∈ Submodule.span (p.1.adicCompletionIntegers X.B.I.F)
      {w | ∃ t ∈ OEp X p, ∃ s ∈ PI.FinKW.vecV X.B.I p.1 '' S, w = t • s}) :
    ∃ A ∈ Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S, PI.FinKW.vecV X.B.I p.1 A = a ∧
      ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v A = 0 := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ⟨τ, hτ, rfl⟩, _, ⟨s, hs, rfl⟩, rfl⟩ := hx
    refine ⟨(scP X p 1 * τ) • s, ?_, ?_, ?_⟩
    · exact Submodule.smul_mem _
        (⟨scP X p 1 * τ, Subring.mul_mem _ (scalarAt_one_mem_integralAdeles X p) hτ⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
        (Submodule.subset_span hs)
    · rw [imA_vecV_smul', map_mul, component_scalarAt_same, map_one, one_mul]
    · intro v hv
      rw [imA_vecV_smul', map_mul, component_scalarAt_of_ne X p v hv, zero_mul, zero_smul]
  | zero => exact ⟨0, zero_mem _, imA_vecV_zero' X p.1, fun v _ => imA_vecV_zero' X v⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    obtain ⟨B, hB, h3, h4⟩ := hy
    exact ⟨A + B, add_mem hA hB, by rw [imA_vecV_add', h1, h3],
      fun v hv => by rw [imA_vecV_add', h2 v hv, h4 v hv, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    refine ⟨scP X p c • A, Submodule.smul_mem _
      (⟨_, scalarAt_mem_integralAdeles X p c⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hA, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, h1, imA_smul_alg]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]

theorem imA_lift_lat (p : TypX X) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ∃ A ∈ X.B.I.Lf, PI.FinKW.vecV X.B.I p.1 A = u ∧ ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v A = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hin : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) ∈ X.B.I.Lf :=
      Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
    refine ⟨scP X p 1 • (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)),
      Submodule.smul_mem _ (⟨_, scalarAt_one_mem_integralAdeles X p⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hin, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, map_one, one_smul]
      funext i
      simp [PI.FinKW.vecV, PI.FinKW.psiV, Formalism.UG.inclE, ratV, inclR]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]
  | zero => exact ⟨0, zero_mem _, imA_vecV_zero' X p.1, fun v _ => imA_vecV_zero' X v⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    obtain ⟨B, hB, h3, h4⟩ := hy
    exact ⟨A + B, add_mem hA hB, by rw [imA_vecV_add', h1, h3],
      fun v hv => by rw [imA_vecV_add', h2 v hv, h4 v hv, add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨A, hA, h1, h2⟩ := hx
    refine ⟨scP X p c • A, Submodule.smul_mem _
      (⟨_, scalarAt_mem_integralAdeles X p c⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hA, ?_, ?_⟩
    · rw [imA_vecV_smul', component_scalarAt_same, h1, imA_smul_alg]
    · intro v hv
      rw [imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul]

end MassDataIdxSteps
end
end

section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem imA_lift_mL (p : TypX X) (m : ℕ) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ Ideal.span {((m : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ∃ A ∈ mL X.B.I m, PI.FinKW.vecV X.B.I p.1 A = u ∧ ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v A = 0 := by
  refine Submodule.smul_induction_on hu ?_ ?_
  · intro r hr n hn
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    obtain ⟨A, hA, h1, h2⟩ := imA_lift_lat X p hn
    have hA' : scP X p a • A ∈ X.B.I.Lf :=
      Submodule.smul_mem _ (⟨_, scalarAt_mem_integralAdeles X p a⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hA
    refine ⟨(m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (scP X p a • A),
      Submodule.subset_span ⟨_, hA', rfl⟩, ?_, ?_⟩
    · rw [imA_vecV_smul', imA_vecV_smul', component_scalarAt_same, h1, smul_smul, imA_smul_alg, map_natCast]
      congr 1
      push_cast
      rw [mul_comm]
    · intro v hv
      rw [imA_vecV_smul', imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul, smul_zero]
  · rintro x y ⟨A, hA, h1, h2⟩ ⟨B, hB, h3, h4⟩
    exact ⟨A + B, add_mem hA hB, by rw [imA_vecV_add', h1, h3],
      fun v hv => by rw [imA_vecV_add', h2 v hv, h4 v hv, add_zero]⟩

theorem imA_inMod_glob (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (hs : ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v w = 0)
    (h : InModP X p m (PI.FinKW.vecV X.B.I p.1 '' S) (PI.FinKW.vecV X.B.I p.1 w)) :
    InMod X.B.I m S w := by
  obtain ⟨a, ha, b, hb', hab⟩ := Submodule.mem_sup.mp h
  obtain ⟨A, hA, h1, h2⟩ := imA_lift_sp X p S ha
  obtain ⟨B, hB, h3, h4⟩ := imA_lift_mL X p m hb'
  have hw : w = A + B := by
    rw [← sub_eq_zero]
    apply imA_vec_ext X
    intro v
    rw [imA_vecV_sub, imA_vecV_add']
    by_cases hv : v = p.1
    · subst hv; rw [h1, h3, hab, sub_self]
    · rw [hs v hv, h2 v hv, h4 v hv, add_zero, sub_zero]
  rw [hw]
  exact Submodule.mem_sup.mpr ⟨A, hA, B, hB, rfl⟩

theorem imA_vecV_mulVec' (v : HeightOneSpectrum (𝓞 X.B.I.F)) (x : X.B.I.Gf)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v ((X.B.I.fmat x - 1) *ᵥ w) =
      (((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (piV X.B.I v (tf X.B.I hb x)) :
        GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I v w := by
  rw [LocIdxLift_vecV_mulVec, Matrix.map_sub _ (map_sub _), LocIdxLift_psiV_fmat X.B.I hb,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem imA_sub_kpp (p : TypX X) : {y | y ∈ KvX X p ∧ LocCong X p y} ⊆ KppX X hb p := by
  rintro y ⟨hy, h1, h2, h3⟩
  obtain ⟨x, hx⟩ := Bridge_tf_surjective X.B.I hb (liftHA X.B.I p.1 y)
  have hcomp : ∀ v, v ≠ p.1 → piV X.B.I v (tf X.B.I hb x) = 1 := fun v h => by
    rw [hx, LocIdxLift_piV_ne X.B.I p.1 v h]
  have hsame : piV X.B.I p.1 (tf X.B.I hb x) = y := by rw [hx, LocIdxLift_piV_same]
  have hsupp : ∀ w, ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v ((X.B.I.fmat x - 1) *ᵥ w) = 0 := by
    intro w v hv
    rw [imA_vecV_mulVec' X hb, hcomp v hv]
    have : ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (1 : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :
        GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = 1 := rfl
    rw [this, sub_self, Matrix.zero_mulVec]
  have hloc : ∀ w, PI.FinKW.vecV X.B.I p.1 ((X.B.I.fmat x - 1) *ᵥ w) =
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J y :
        GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 w := by
    intro w; rw [imA_vecV_mulVec' X hb, hsame]
  have hxK : x ∈ X.B.I.Kset := by
    rw [← Bridge_mem_Kf_iff X.B.I hb, Kf, Subgroup.mem_iInf]
    intro v
    show HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (piV X.B.I v (tf X.B.I hb x)) ∈
      Kloc v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    by_cases h : v = p.1
    · subst h; rw [hsame]; exact hy
    · rw [hcomp v h]; exact (Kloc v _).one_mem
  have hc : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x := by
    refine ⟨fun a => ?_, ?_, fun i => ?_⟩
    · apply imA_inMod_glob X p _ _ _ (hsupp _)
      rw [hloc, Set.image_image]; exact h1 a
    · apply imA_inMod_glob X p _ _ _ (hsupp _)
      rw [hloc, ← Set.range_comp]; exact h2
    · apply imA_inMod_glob X p _ _ _ (hsupp _)
      rw [hloc, Set.image_union, Set.image_image, ← Set.range_comp]; exact h3 i
  exact ⟨tf X.B.I hb x, ⟨x, ⟨hxK, hc⟩, rfl⟩, hsame⟩

theorem stImAloc_holds (p : TypX X) : StImAloc X hb p :=
  Set.Subset.antisymm (imA_kpp_sub X hb p) (imA_sub_kpp X hb p)

end MassDataIdxSteps
end
end
