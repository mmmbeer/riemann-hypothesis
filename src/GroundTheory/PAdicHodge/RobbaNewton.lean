import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.PerfectoidField

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem Laurent.convergesAt_single {K : Type*} [NontriviallyNormedField K] (n₀ : ℤ) (k : K)
    (ρ : ℝ) : ConvergesAt (Pi.single n₀ k) ρ := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(Set.finite_singleton n₀).compl_mem_cofinite] with n hn
  simp [Pi.single_apply, show n ≠ n₀ from hn]

@[ext]
structure AnnulusRing (I : Set ℝ) where

  coeff : ℤ → K
  convergesAt' : ∀ ρ ∈ I, 0 < ρ → ConvergesAt coeff ρ

@[ext]
structure Robba where

  coeff : ℤ → K
  exists_convergesAt' : ∃ r < 1, ∀ ρ, r ≤ ρ → ρ < 1 → 0 < ρ → ConvergesAt coeff ρ

variable {K}

namespace AnnulusRing

variable {I : Set ℝ}

theorem convergesAt (f : AnnulusRing K I) {ρ : ℝ} (hρ : ρ ∈ I) (hρ0 : 0 < ρ) :
    ConvergesAt f.coeff ρ :=
  f.convergesAt' ρ hρ hρ0

theorem coeff_injective : Function.Injective (coeff : AnnulusRing K I → ℤ → K) :=
  fun _ _ h => AnnulusRing.ext h

instance : Zero (AnnulusRing K I) := ⟨⟨0, fun _ _ _ => convergesAt_zero⟩⟩
instance : One (AnnulusRing K I) := ⟨⟨Pi.single 0 1, fun ρ _ _ => convergesAt_single 0 1 ρ⟩⟩
instance : Add (AnnulusRing K I) :=
  ⟨fun f g => ⟨f.coeff + g.coeff, fun ρ h h0 => (f.convergesAt h h0).add h0 (g.convergesAt h h0)⟩⟩
instance : Neg (AnnulusRing K I) := ⟨fun f => ⟨-f.coeff, fun ρ h h0 => (f.convergesAt h h0).neg⟩⟩
instance : Sub (AnnulusRing K I) :=
  ⟨fun f g => ⟨f.coeff - g.coeff, fun ρ h h0 => (f.convergesAt h h0).sub h0 (g.convergesAt h h0)⟩⟩
instance : SMul K (AnnulusRing K I) :=
  ⟨fun k f => ⟨k • f.coeff, fun ρ h h0 => (f.convergesAt h h0).smul k⟩⟩
instance : SMul ℕ (AnnulusRing K I) :=
  ⟨fun k f => ⟨k • f.coeff, fun ρ h h0 => by
    simpa [ConvergesAt, nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K] using
      (f.convergesAt h h0).smul (k : K)⟩⟩
instance : SMul ℤ (AnnulusRing K I) :=
  ⟨fun k f => ⟨k • f.coeff, fun ρ h h0 => by
    simpa [ConvergesAt, zsmul_eq_mul, ← Int.cast_smul_eq_zsmul K] using
      (f.convergesAt h h0).smul (k : K)⟩⟩
instance : Mul (AnnulusRing K I) :=
  ⟨fun f g => ⟨cmul f.coeff g.coeff, fun ρ h h0 => (f.convergesAt h h0).cmul h0 (g.convergesAt h h0)⟩⟩

@[simp] theorem coeff_zero : (0 : AnnulusRing K I).coeff = 0 := rfl
@[simp] theorem coeff_one : (1 : AnnulusRing K I).coeff = Pi.single 0 1 := rfl
@[simp] theorem coeff_add (f g : AnnulusRing K I) : (f + g).coeff = f.coeff + g.coeff := rfl
@[simp] theorem coeff_neg (f : AnnulusRing K I) : (-f).coeff = -f.coeff := rfl
@[simp] theorem coeff_sub (f g : AnnulusRing K I) : (f - g).coeff = f.coeff - g.coeff := rfl
@[simp] theorem coeff_smul (k : K) (f : AnnulusRing K I) : (k • f).coeff = k • f.coeff := rfl
@[simp] theorem coeff_nsmul (k : ℕ) (f : AnnulusRing K I) : (k • f).coeff = k • f.coeff := rfl
@[simp] theorem coeff_zsmul (k : ℤ) (f : AnnulusRing K I) : (k • f).coeff = k • f.coeff := rfl
theorem coeff_mul (f g : AnnulusRing K I) : (f * g).coeff = cmul f.coeff g.coeff := rfl

instance : AddCommGroup (AnnulusRing K I) :=
  coeff_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

variable [hI : Fact (∃ ρ ∈ I, 0 < ρ)]

def radius (I : Set ℝ) [hI : Fact (∃ ρ ∈ I, 0 < ρ)] : ℝ := hI.out.choose

theorem radius_mem : radius I ∈ I := hI.out.choose_spec.1

theorem radius_pos : 0 < radius I := hI.out.choose_spec.2

theorem conv (f : AnnulusRing K I) : ConvergesAt f.coeff (radius I) :=
  f.convergesAt radius_mem radius_pos

instance : CommRing (AnnulusRing K I) :=
  { (inferInstance : AddCommGroup (AnnulusRing K I)) with
    mul_assoc := fun f g h => AnnulusRing.ext (cmul_assoc radius_pos f.conv g.conv h.conv)
    one_mul := fun f => AnnulusRing.ext (single_zero_one_cmul f.coeff)
    mul_one := fun f => AnnulusRing.ext (cmul_single_zero_one f.coeff)
    left_distrib := fun f g h => AnnulusRing.ext (cmul_add radius_pos f.conv g.conv h.conv)
    right_distrib := fun f g h => AnnulusRing.ext (add_cmul radius_pos f.conv g.conv h.conv)
    zero_mul := fun f => AnnulusRing.ext (zero_cmul f.coeff)
    mul_zero := fun f => AnnulusRing.ext (cmul_zero f.coeff)
    mul_comm := fun f g => AnnulusRing.ext (cmul_comm f.coeff g.coeff) }

def coeffHom : AnnulusRing K I →+ (ℤ → K) where
  toFun := coeff
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module K (AnnulusRing K I) :=
  Function.Injective.module K coeffHom coeff_injective fun _ _ => rfl

instance : Algebra K (AnnulusRing K I) :=
  Algebra.ofModule (fun k f g => AnnulusRing.ext (smul_cmul k f.coeff g.coeff))
    (fun k f g => AnnulusRing.ext (cmul_smul k f.coeff g.coeff))

def T : AnnulusRing K I := ⟨Pi.single 1 1, fun ρ _ _ => convergesAt_single 1 1 ρ⟩

def restrict {J : Set ℝ} [Fact (∃ ρ ∈ J, 0 < ρ)] (hJ : J ⊆ I) : AnnulusRing K I →ₐ[K] AnnulusRing K J where
  toFun f := ⟨f.coeff, fun ρ h h0 => f.convergesAt (hJ h) h0⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem coeff_restrict {J : Set ℝ} [Fact (∃ ρ ∈ J, 0 < ρ)] (hJ : J ⊆ I)
    (f : AnnulusRing K I) : (restrict hJ f).coeff = f.coeff := rfl

end AnnulusRing

abbrev AnnulusRing.halfOpen (K : Type*) [NontriviallyNormedField K] (r : ℝ) :=
  AnnulusRing K (Set.Ico r 1)

instance AnnulusRing.fact_ico {r : ℝ} [hr : Fact (r < 1)] : Fact (∃ ρ ∈ Set.Ico r 1, 0 < ρ) :=
  ⟨⟨max r (1 / 2), ⟨le_max_left _ _, max_lt hr.out (by norm_num)⟩,
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)⟩⟩

namespace Robba

theorem coeff_injective : Function.Injective (coeff : Robba K → ℤ → K) :=
  fun _ _ h => Robba.ext h

theorem exists_common (f g : Robba K) : ∃ r, 0 < r ∧ r < 1 ∧ ∀ ρ, r ≤ ρ → ρ < 1 →
    ConvergesAt f.coeff ρ ∧ ConvergesAt g.coeff ρ := by
  obtain ⟨r₁, hr₁, h₁⟩ := f.exists_convergesAt'
  obtain ⟨r₂, hr₂, h₂⟩ := g.exists_convergesAt'
  refine ⟨max (max r₁ r₂) (1 / 2), by positivity, max_lt (max_lt hr₁ hr₂) (by norm_num),
    fun ρ hρ hρ1 => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans hρ)
  exact ⟨h₁ ρ ((le_max_left _ _).trans ((le_max_left _ _).trans hρ)) hρ1 hρ0,
    h₂ ρ ((le_max_right _ _).trans ((le_max_left _ _).trans hρ)) hρ1 hρ0⟩

theorem exists_common₃ (f g h : Robba K) : ∃ ρ, 0 < ρ ∧ ConvergesAt f.coeff ρ ∧
    ConvergesAt g.coeff ρ ∧ ConvergesAt h.coeff ρ := by
  obtain ⟨r, hr0, hr1, hfg⟩ := exists_common f g
  obtain ⟨s, hs0, hs1, hgh⟩ := exists_common g h
  refine ⟨max r s, lt_max_of_lt_left hr0, (hfg _ (le_max_left _ _) (max_lt hr1 hs1)).1,
    (hfg _ (le_max_left _ _) (max_lt hr1 hs1)).2, (hgh _ (le_max_right _ _) (max_lt hr1 hs1)).2⟩

instance : Zero (Robba K) := ⟨⟨0, ⟨0, one_pos, fun _ _ _ _ => convergesAt_zero⟩⟩⟩
instance : One (Robba K) := ⟨⟨Pi.single 0 1, ⟨0, one_pos, fun ρ _ _ _ => convergesAt_single 0 1 ρ⟩⟩⟩
instance : Add (Robba K) :=
  ⟨fun f g => ⟨f.coeff + g.coeff, by
    obtain ⟨r, hr0, hr1, h⟩ := exists_common f g
    exact ⟨r, hr1, fun ρ h1 h2 h3 => (h ρ h1 h2).1.add h3 (h ρ h1 h2).2⟩⟩⟩
instance : Neg (Robba K) :=
  ⟨fun f => ⟨-f.coeff, by
    obtain ⟨r, hr, h⟩ := f.exists_convergesAt'
    exact ⟨r, hr, fun ρ h1 h2 h3 => (h ρ h1 h2 h3).neg⟩⟩⟩
instance : Sub (Robba K) :=
  ⟨fun f g => ⟨f.coeff - g.coeff, by
    obtain ⟨r, hr0, hr1, h⟩ := exists_common f g
    exact ⟨r, hr1, fun ρ h1 h2 h3 => (h ρ h1 h2).1.sub h3 (h ρ h1 h2).2⟩⟩⟩
instance : SMul K (Robba K) :=
  ⟨fun k f => ⟨k • f.coeff, by
    obtain ⟨r, hr, h⟩ := f.exists_convergesAt'
    exact ⟨r, hr, fun ρ h1 h2 h3 => (h ρ h1 h2 h3).smul k⟩⟩⟩
instance : SMul ℕ (Robba K) :=
  ⟨fun k f => ⟨k • f.coeff, by
    obtain ⟨r, hr, h⟩ := f.exists_convergesAt'
    exact ⟨r, hr, fun ρ h1 h2 h3 => by
      simpa [ConvergesAt, nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K] using
        (h ρ h1 h2 h3).smul (k : K)⟩⟩⟩
instance : SMul ℤ (Robba K) :=
  ⟨fun k f => ⟨k • f.coeff, by
    obtain ⟨r, hr, h⟩ := f.exists_convergesAt'
    exact ⟨r, hr, fun ρ h1 h2 h3 => by
      simpa [ConvergesAt, zsmul_eq_mul, ← Int.cast_smul_eq_zsmul K] using
        (h ρ h1 h2 h3).smul (k : K)⟩⟩⟩
instance : Mul (Robba K) :=
  ⟨fun f g => ⟨cmul f.coeff g.coeff, by
    obtain ⟨r, hr0, hr1, h⟩ := exists_common f g
    exact ⟨r, hr1, fun ρ h1 h2 h3 => (h ρ h1 h2).1.cmul h3 (h ρ h1 h2).2⟩⟩⟩

@[simp] theorem coeff_zero : (0 : Robba K).coeff = 0 := rfl
@[simp] theorem coeff_one : (1 : Robba K).coeff = Pi.single 0 1 := rfl
@[simp] theorem coeff_add (f g : Robba K) : (f + g).coeff = f.coeff + g.coeff := rfl
@[simp] theorem coeff_neg (f : Robba K) : (-f).coeff = -f.coeff := rfl
@[simp] theorem coeff_sub (f g : Robba K) : (f - g).coeff = f.coeff - g.coeff := rfl
@[simp] theorem coeff_smul (k : K) (f : Robba K) : (k • f).coeff = k • f.coeff := rfl
theorem coeff_mul (f g : Robba K) : (f * g).coeff = cmul f.coeff g.coeff := rfl

instance : AddCommGroup (Robba K) :=
  coeff_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : CommRing (Robba K) :=
  { (inferInstance : AddCommGroup (Robba K)) with
    mul_assoc := fun f g h => by
      obtain ⟨ρ, hρ, hf, hg, hh⟩ := exists_common₃ f g h
      exact Robba.ext (cmul_assoc hρ hf hg hh)
    one_mul := fun f => Robba.ext (single_zero_one_cmul f.coeff)
    mul_one := fun f => Robba.ext (cmul_single_zero_one f.coeff)
    left_distrib := fun f g h => by
      obtain ⟨ρ, hρ, hf, hg, hh⟩ := exists_common₃ f g h
      exact Robba.ext (cmul_add hρ hf hg hh)
    right_distrib := fun f g h => by
      obtain ⟨ρ, hρ, hf, hg, hh⟩ := exists_common₃ f g h
      exact Robba.ext (add_cmul hρ hf hg hh)
    zero_mul := fun f => Robba.ext (zero_cmul f.coeff)
    mul_zero := fun f => Robba.ext (cmul_zero f.coeff)
    mul_comm := fun f g => Robba.ext (cmul_comm f.coeff g.coeff) }

def coeffHom : Robba K →+ (ℤ → K) where
  toFun := coeff
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Module K (Robba K) :=
  Function.Injective.module K coeffHom coeff_injective fun _ _ => rfl

instance : Algebra K (Robba K) :=
  Algebra.ofModule (fun k f g => Robba.ext (smul_cmul k f.coeff g.coeff))
    (fun k f g => Robba.ext (cmul_smul k f.coeff g.coeff))

end Robba

namespace AnnulusRing

variable {r : ℝ} [Fact (r < 1)]

def toRobba : AnnulusRing.halfOpen K r →ₐ[K] Robba K where
  toFun f := ⟨f.coeff, ⟨r, Fact.out, fun ρ h1 h2 h3 => f.convergesAt ⟨h1, h2⟩ h3⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem coeff_toRobba (f : AnnulusRing.halfOpen K r) : (toRobba f).coeff = f.coeff := rfl



end AnnulusRing

namespace Robba


end Robba

namespace Laurent

theorem gaussNorm_single_zero_one {ρ : ℝ} (hρ : 0 < ρ) :
    gaussNorm (Pi.single 0 (1 : K)) ρ = 1 := by
  refine le_antisymm (gaussNorm_le fun n => ?_) ?_
  · by_cases hn : n = 0
    · subst hn; simp
    · simp [Pi.single_apply, hn]
  · simpa using (convergesAt_single 0 (1 : K) ρ).le_gaussNorm 0

theorem domSet_single_zero_one {ρ : ℝ} (hρ : 0 < ρ) :
    domSet (Pi.single 0 (1 : K)) ρ = {0} := by
  ext n
  simp only [domSet, Set.mem_setOf_eq, gaussNorm_single_zero_one hρ, Set.mem_singleton_iff]
  by_cases hn : n = 0
  · subst hn; simp
  · simp [Pi.single_apply, hn]

theorem lowIndex_single_zero_one {ρ : ℝ} (hρ : 0 < ρ) :
    lowIndex (Pi.single 0 (1 : K)) ρ = 0 := by
  rw [lowIndex, domSet_single_zero_one hρ, csInf_singleton]

theorem highIndex_single_zero_one {ρ : ℝ} (hρ : 0 < ρ) :
    highIndex (Pi.single 0 (1 : K)) ρ = 0 := by
  rw [highIndex, domSet_single_zero_one hρ, csSup_singleton]

end Laurent

namespace Robba

def bounded (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    Subring (Robba K) where
  carrier := {f | BddAbove (Set.range fun n => ‖f.coeff n‖)}
  mul_mem' {f g} hf hg := by
    obtain ⟨A, hA⟩ := hf
    obtain ⟨B, hB⟩ := hg
    refine ⟨max A 0 * max B 0, Set.forall_mem_range.2 fun n => ?_⟩
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_
    rw [norm_mul]
    exact mul_le_mul ((hA ⟨i, rfl⟩).trans (le_max_left _ _))
      ((hB ⟨n - i, rfl⟩).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  one_mem' := ⟨1, Set.forall_mem_range.2 fun n => by
    by_cases hn : n = 0
    · subst hn; simp
    · simp [Pi.single_apply, hn]⟩
  add_mem' {f g} hf hg := by
    obtain ⟨A, hA⟩ := hf
    obtain ⟨B, hB⟩ := hg
    exact ⟨A + B, Set.forall_mem_range.2 fun n =>
      (norm_add_le _ _).trans (add_le_add (hA ⟨n, rfl⟩) (hB ⟨n, rfl⟩))⟩
  zero_mem' := ⟨0, Set.forall_mem_range.2 fun n => by simp⟩
  neg_mem' {f} hf := by
    obtain ⟨A, hA⟩ := hf
    exact ⟨A, Set.forall_mem_range.2 fun n => by simpa using hA ⟨n, rfl⟩⟩


theorem mem_bounded_of_mul_eq_one {f g : Robba K} (h : f * g = 1) : f ∈ bounded K := by
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f g
  have hfg : cmul f.coeff g.coeff = Pi.single 0 1 := congrArg Robba.coeff h
  have hne : (Pi.single 0 (1 : K) : ℤ → K) ≠ 0 := fun h0 => by
    simpa using congrFun h0 0
  have hf0 : f.coeff ≠ 0 := fun h0 => hne (by rw [← hfg, h0, zero_cmul])
  have hg0 : g.coeff ≠ 0 := fun h0 => hne (by rw [← hfg, h0, cmul_zero])
  have pos : ∀ ρ, r ≤ ρ → 0 < ρ := fun ρ hρ => hr0.trans_le hρ

  have key : ∀ ρ, r ≤ ρ → ρ < 1 → lowIndex f.coeff ρ = highIndex f.coeff ρ ∧
      lowIndex g.coeff ρ = -lowIndex f.coeff ρ ∧ highIndex g.coeff ρ = -lowIndex f.coeff ρ := by
    intro ρ h1 h2
    have hρ := pos ρ h1
    obtain ⟨cf, cg⟩ := hc ρ h1 h2
    have e1 := lowIndex_cmul hρ cf cg hf0 hg0
    have e2 := highIndex_cmul hρ cf cg hf0 hg0
    rw [hfg, lowIndex_single_zero_one hρ] at e1
    rw [hfg, highIndex_single_zero_one hρ] at e2
    have l1 := lowIndex_le_highIndex hρ cf hf0
    have l2 := lowIndex_le_highIndex hρ cg hg0
    refine ⟨by omega, by omega, by omega⟩

  have mono : ∀ ρ ρ', r ≤ ρ → ρ < ρ' → ρ' < 1 → lowIndex f.coeff ρ = lowIndex f.coeff ρ' := by
    intro ρ ρ' h1 h12 h2
    have h1' : r ≤ ρ' := h1.trans h12.le
    have hρ1 : ρ < 1 := h12.trans h2
    have a1 := highIndex_le_lowIndex (pos ρ h1) h12 (hc ρ h1 hρ1).1 (hc ρ' h1' h2).1 hf0
    have a2 := highIndex_le_lowIndex (pos ρ h1) h12 (hc ρ h1 hρ1).2 (hc ρ' h1' h2).2 hg0
    obtain ⟨k1, k2, k3⟩ := key ρ h1 hρ1
    obtain ⟨k1', k2', k3'⟩ := key ρ' h1' h2
    omega
  set N := lowIndex f.coeff r
  have hN : ∀ ρ, r ≤ ρ → ρ < 1 → ∀ n, ‖f.coeff n‖ * ρ ^ n ≤ ‖f.coeff N‖ * ρ ^ N := by
    intro ρ h1 h2 n
    have hL : lowIndex f.coeff ρ = N := by
      rcases h1.lt_or_eq with h | h
      · exact (mono r ρ le_rfl h h2).symm
      · subst h; rfl
    have hmem := lowIndex_mem (pos ρ h1) (hc ρ h1 h2).1 hf0
    rw [hL] at hmem
    rw [show ‖f.coeff N‖ * ρ ^ N = gaussNorm f.coeff ρ from hmem]
    exact (hc ρ h1 h2).1.le_gaussNorm n
  refine ⟨‖f.coeff N‖, Set.forall_mem_range.2 fun n => ?_⟩
  have hlim : Tendsto (fun ρ : ℝ => ‖f.coeff N‖ * ρ ^ (N - n)) (𝓝[<] 1)
      (𝓝 (‖f.coeff N‖ * (1 : ℝ) ^ (N - n))) :=
    (((continuousAt_zpow₀ (1 : ℝ) (N - n) (Or.inl one_ne_zero)).tendsto).const_mul _).mono_left
      nhdsWithin_le_nhds
  rw [one_zpow, mul_one] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hr1] with ρ hρ
  have hρ0 := pos ρ hρ.1.le
  have := hN ρ hρ.1.le hρ.2 n
  have hpos : 0 < ρ ^ n := zpow_pos hρ0 n
  rw [show ρ ^ (N - n) = ρ ^ N / ρ ^ n by rw [zpow_sub₀ hρ0.ne'], mul_div_assoc',
    le_div_iff₀ hpos]
  exact this

theorem isUnit_iff {f : Robba K} :
    IsUnit f ↔ ∃ g : (bounded K)ˣ, ((g : bounded K) : Robba K) = f := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : (u : Robba K) ∈ bounded K := mem_bounded_of_mul_eq_one u.mul_inv
    have h2 : ((u⁻¹ : (Robba K)ˣ) : Robba K) ∈ bounded K := mem_bounded_of_mul_eq_one u.inv_mul
    exact ⟨⟨⟨u, h1⟩, ⟨_, h2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact (Units.map (bounded K).subtype.toMonoidHom g).isUnit


end Robba

namespace Laurent

theorem cmul_single_left (k : ℤ) (c : K) (x : ℤ → K) :
    cmul (Pi.single k c) x = fun n => c * x (n - k) := by
  funext n
  unfold cmul
  rw [tsum_eq_single k fun i hi => by simp [Pi.single_apply, hi]]
  simp

end Laurent

namespace Robba

def single (k : ℤ) (c : K) : Robba K :=
  ⟨Pi.single k c, ⟨0, one_pos, fun ρ _ _ _ => convergesAt_single k c ρ⟩⟩

@[simp] theorem coeff_single (k : ℤ) (c : K) : (single k c).coeff = Pi.single k c := rfl

theorem coeff_single_mul (k : ℤ) (c : K) (f : Robba K) :
    (single k c * f).coeff = fun n => c * f.coeff (n - k) :=
  cmul_single_left k c f.coeff

theorem single_mul_single (k l : ℤ) (c d : K) : single k c * single l d = single (k + l) (c * d) := by
  ext n
  rw [coeff_single_mul]
  simp only [coeff_single, Pi.single_apply, sub_eq_iff_eq_add]
  split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | simp

@[simp] theorem single_zero_one : single 0 (1 : K) = 1 := rfl

theorem isUnit_single (k : ℤ) {c : K} (hc : c ≠ 0) : IsUnit (single k c) := by
  have h : single k c * single (-k) c⁻¹ = 1 := by
    rw [single_mul_single, add_neg_cancel, mul_inv_cancel₀ hc, single_zero_one]
  exact ⟨⟨single k c, single (-k) c⁻¹, h, by rw [mul_comm]; exact h⟩, rfl⟩

def T : Robba K := single 1 1

theorem single_mem_bounded (k : ℤ) (c : K) : single k c ∈ bounded K :=
  ⟨‖c‖, Set.forall_mem_range.2 fun n => by
    by_cases hn : n = k
    · subst hn; simp
    · simp [Pi.single_apply, hn]⟩

end Robba

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

variable {a b u : ℤ → K} {ρ : ℝ}

theorem gaussNorm_cmul_le (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) :
    gaussNorm (cmul a b) ρ ≤ gaussNorm a ρ * gaussNorm b ρ :=
  gaussNorm_le fun n => norm_cmul_mul_zpow_le hρ
    (mul_nonneg (gaussNorm_nonneg hρ) (gaussNorm_nonneg hρ)) fun i =>
      mul_le_mul (ha.le_gaussNorm i) (hb.le_gaussNorm _) (by positivity) (gaussNorm_nonneg hρ)

def cpow (u : ℤ → K) : ℕ → ℤ → K
  | 0 => Pi.single 0 1
  | k + 1 => cmul u (cpow u k)

theorem ConvergesAt.cpow (hρ : 0 < ρ) (hu : ConvergesAt u ρ) : ∀ k, ConvergesAt (cpow u k) ρ
  | 0 => convergesAt_single 0 1 ρ
  | k + 1 => hu.cmul hρ (hu.cpow hρ k)

theorem gaussNorm_cpow_le (hρ : 0 < ρ) (hu : ConvergesAt u ρ) :
    ∀ k, gaussNorm (cpow u k) ρ ≤ gaussNorm u ρ ^ k
  | 0 => by simp [cpow, gaussNorm_single_zero_one hρ]
  | k + 1 => by
    rw [pow_succ']
    exact (gaussNorm_cmul_le hρ hu (hu.cpow hρ k)).trans
      (mul_le_mul_of_nonneg_left (gaussNorm_cpow_le hρ hu k) (gaussNorm_nonneg hρ))

theorem weight_cpow_le (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (k : ℕ) (n : ℤ) :
    ‖cpow u k n‖ * ρ ^ n ≤ gaussNorm u ρ ^ k :=
  ((hu.cpow hρ k).le_gaussNorm n).trans (gaussNorm_cpow_le hρ hu k)

def geomInv (u : ℤ → K) : ℤ → K := fun n => ∑' k : ℕ, (-1) ^ k * cpow u k n

theorem norm_geom_term_le (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (k : ℕ) (n : ℤ) :
    ‖(-1) ^ k * cpow u k n‖ ≤ gaussNorm u ρ ^ k / ρ ^ n := by
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, le_div_iff₀ (zpow_pos hρ n)]
  exact weight_cpow_le hρ hu k n

theorem tendsto_geom_term (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (hq : gaussNorm u ρ < 1) (n : ℤ) :
    Tendsto (fun k : ℕ => (-1) ^ k * cpow u k n) cofinite (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero, Nat.cofinite_eq_atTop]
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (gaussNorm_nonneg hρ) hq).div_const (ρ ^ n)
  rw [zero_div] at h
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => norm_geom_term_le hρ hu k n) h

theorem ConvergesAt.geomInv (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (hq : gaussNorm u ρ < 1) :
    ConvergesAt (geomInv u) ρ := by
  refine tendsto_order.2 ⟨fun x hx => Eventually.of_forall fun n =>
    lt_of_lt_of_le hx (by positivity), fun ε hε => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (half_pos hε) hq
  have hS : (⋃ k ∈ Finset.range k₀, {n : ℤ | ε / 2 ≤ ‖Laurent.cpow u k n‖ * ρ ^ n}).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun k _ => (hu.cpow hρ k).finite_le (half_pos hε)
  refine Filter.eventually_cofinite.2 (hS.subset fun n hn => ?_)
  simp only [Set.mem_setOf_eq, not_lt] at hn
  by_contra hcon
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, not_exists, not_and, not_le]
    at hcon
  have hρn : 0 < ρ ^ n := zpow_pos hρ n
  have : ‖Laurent.geomInv u n‖ * ρ ^ n ≤ ε / 2 := by
    rw [← le_div_iff₀ hρn]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, le_div_iff₀ hρn]
    rcases lt_or_ge k k₀ with hk | hk
    · exact (hcon k hk).le
    · exact (weight_cpow_le hρ hu k n).trans ((pow_le_pow_of_le_one (gaussNorm_nonneg hρ)
        hq.le hk).trans hk₀.le)
  linarith

theorem cmul_one_add_geomInv (hρ : 0 < ρ) (hu : ConvergesAt u ρ) (hq : gaussNorm u ρ < 1) :
    cmul (Pi.single 0 1 + u) (geomInv u) = Pi.single 0 1 := by
  have hw := hu.geomInv hρ hq
  rw [add_cmul hρ (convergesAt_single 0 1 ρ) hu hw, single_zero_one_cmul]
  funext n
  have hsum : Summable (Function.uncurry fun i (k : ℕ) => u i * ((-1) ^ k * cpow u k (n - i))) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hq' : Tendsto (fun k : ℕ => gaussNorm u ρ ^ k) cofinite (𝓝 0) := by
      rw [Nat.cofinite_eq_atTop]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (gaussNorm_nonneg hρ) hq
    have h := (tendsto_mul_cofinite_nhds_zero hu hq').div_const (ρ ^ n)
    rw [zero_div] at h
    refine squeeze_zero (fun _ => norm_nonneg _) (fun ⟨i, k⟩ => ?_) h
    simp only [Function.uncurry_apply_pair, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul]
    have hρn : 0 < ρ ^ n := zpow_pos hρ n
    rw [le_div_iff₀ hρn]
    have e : ρ ^ n = ρ ^ i * ρ ^ (n - i) := by rw [← zpow_add₀ hρ.ne']; congr 1; ring
    rw [e]
    have h1 := weight_cpow_le hρ hu k (n - i)
    calc ‖u i‖ * ‖cpow u k (n - i)‖ * (ρ ^ i * ρ ^ (n - i))
        = (‖u i‖ * ρ ^ i) * (‖cpow u k (n - i)‖ * ρ ^ (n - i)) := by ring
      _ ≤ (‖u i‖ * ρ ^ i) * gaussNorm u ρ ^ k :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
  have e1 : cmul u (geomInv u) n = ∑' k : ℕ, (-1) ^ k * cpow u (k + 1) n := by
    simp only [cmul, geomInv, cpow]
    simp_rw [← tsum_mul_left]
    rw [← hsum.tsum_comm]
    congr 1; funext k
    congr 1; funext i; ring
  have e2 : geomInv u n = (Pi.single 0 (1 : K) : ℤ → K) n - ∑' k : ℕ, (-1) ^ k * cpow u (k + 1) n := by
    unfold geomInv
    rw [NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (tendsto_geom_term hρ hu hq n) |>.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, cpow, pow_succ, mul_neg, mul_one, neg_mul, tsum_neg]
    ring
  rw [Pi.add_apply, e1, e2, Pi.single_apply]
  ring

end Laurent

namespace Robba

instance : Nontrivial (Robba K) :=
  ⟨⟨0, 1, fun h => by simpa using congrFun (congrArg Robba.coeff h) 0⟩⟩

theorem isUnit_one_add {U : Robba K} {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hU : ∀ ρ, s ≤ ρ → ρ < 1 → ConvergesAt U.coeff ρ ∧ gaussNorm U.coeff ρ < 1) :
    IsUnit (1 + U) := by
  let W : Robba K := ⟨geomInv U.coeff, ⟨s, hs1, fun ρ h1 h2 h3 =>
    (hU ρ h1 h2).1.geomInv h3 (hU ρ h1 h2).2⟩⟩
  have h : (1 + U) * W = 1 :=
    Robba.ext (cmul_one_add_geomInv hs0 (hU s le_rfl hs1).1 (hU s le_rfl hs1).2)
  exact ⟨⟨_, W, h, by rw [mul_comm]; exact h⟩, rfl⟩

end Robba

theorem exists_norm_le_mul_of_lt [IsDiscreteValuationRing (normInteger K)] :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ x y : K, ‖y‖ < ‖x‖ → ‖y‖ ≤ q * ‖x‖ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (normInteger K)
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hunit : ∀ z : normInteger K, IsUnit z ↔ ‖(z : K)‖ = 1 := by
    intro z
    rw [normInteger_integers.isUnit_iff_valuation_eq_one, NormedField.valuation_apply,
      ← NNReal.coe_eq_one]
    rfl
  have hϖ1 : ‖(ϖ : K)‖ < 1 :=
    lt_of_le_of_ne (mem_normInteger.1 ϖ.2) fun h => hϖ.not_isUnit ((hunit ϖ).2 h)
  refine ⟨‖(ϖ : K)‖, norm_nonneg _, hϖ1, fun x y hxy => ?_⟩
  have hx : x ≠ 0 := by
    rintro rfl
    simp only [norm_zero] at hxy
    exact absurd hxy (not_lt.2 (norm_nonneg _))
  have hz : ‖y / x‖ < 1 := by rw [norm_div, div_lt_one (norm_pos_iff.2 hx)]; exact hxy
  let z : normInteger K := ⟨y / x, mem_normInteger.2 hz.le⟩
  have hzmem : z ∈ IsLocalRing.maximalIdeal (normInteger K) :=
    (IsLocalRing.mem_maximalIdeal z).2 (mem_nonunits_iff.2 fun hu => hz.ne ((hunit z).1 hu))
  rw [hmax, Ideal.mem_span_singleton'] at hzmem
  obtain ⟨t, ht⟩ := hzmem
  have e : y / x = (t : K) * (ϖ : K) := (congrArg Subtype.val ht).symm
  have ht1 : ‖(t : K)‖ ≤ 1 := mem_normInteger.1 t.2
  have : ‖y‖ = ‖y / x‖ * ‖x‖ := by rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.2 hx)]
  rw [this, e, norm_mul]
  calc ‖(t : K)‖ * ‖(ϖ : K)‖ * ‖x‖ = ‖(t : K)‖ * (‖(ϖ : K)‖ * ‖x‖) := by ring
    _ ≤ 1 * (‖(ϖ : K)‖ * ‖x‖) := mul_le_mul_of_nonneg_right ht1 (by positivity)
    _ = ‖(ϖ : K)‖ * ‖x‖ := one_mul _

namespace Robba

variable [IsDiscreteValuationRing (normInteger K)]

theorem isUnit_of_mem_bounded {f : Robba K} (hf : f ∈ bounded K) (h0 : f ≠ 0) : IsUnit f := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_norm_le_mul_of_lt (K := K)
  set a := f.coeff with ha_def
  have ha0 : a ≠ 0 := fun h => h0 (Robba.ext h)
  obtain ⟨n₀, hn₀⟩ := Function.ne_iff.1 ha0
  have hbdd : BddAbove (Set.range fun n => ‖a n‖) := hf
  obtain ⟨r, hr0, hr1, hc⟩ := exists_common f f

  obtain ⟨N, hN⟩ : ∃ N, ∀ n, ‖a n‖ ≤ ‖a N‖ := by
    have hMpos : 0 < ⨆ n, ‖a n‖ := lt_of_lt_of_le (norm_pos_iff.2 hn₀) (le_ciSup hbdd n₀)
    have hlt : q * ⨆ n, ‖a n‖ < ⨆ n, ‖a n‖ := by nlinarith
    obtain ⟨n₁, hn₁⟩ := exists_lt_of_lt_ciSup hlt
    refine ⟨n₁, fun n => not_lt.1 fun hn => ?_⟩
    have := hq _ _ hn
    have := le_ciSup hbdd n
    nlinarith
  set M := ‖a N‖
  have hM : 0 < M := lt_of_lt_of_le (norm_pos_iff.2 hn₀) (hN n₀)

  set S := {n | ‖a n‖ = M}
  have hF := (hc r le_rfl hr1).1.finite_le hM
  obtain ⟨B, hB⟩ := hF.bddBelow
  have hSbdd : BddBelow S := ⟨min B 0, fun n hn => by
    rcases le_or_gt n 0 with h | h
    · refine min_le_of_left_le (hB ?_)
      simp only [Set.mem_setOf_eq]
      have : (1 : ℝ) ≤ r ^ n := one_le_zpow_of_nonpos₀ hr0 hr1.le h
      have hn : ‖a n‖ = M := hn
      nlinarith
    · exact (min_le_right _ _).trans h.le⟩
  set m := sInf S
  have hmS : ‖a m‖ = M := Int.csInf_mem (s := S) ⟨N, rfl⟩ hSbdd
  have hbelow : ∀ n < m, ‖a n‖ < M := fun n hn =>
    lt_of_le_of_ne (hN n) fun h => absurd (csInf_le hSbdd h) (not_le.2 hn)
  have ham : a m ≠ 0 := fun h => by rw [h, norm_zero] at hmS; linarith

  have hMr : 0 < M * r ^ m := by positivity
  have hG := (hc r le_rfl hr1).1.finite_le hMr
  obtain ⟨B', hB'⟩ := hG.bddBelow
  set D := (m - B').toNat
  obtain ⟨ρ₀, hρ₀r, hρ₀1, hρ₀q⟩ : ∃ ρ₀, r ≤ ρ₀ ∧ ρ₀ < 1 ∧ q < ρ₀ ^ D := by
    have hlim : Tendsto (fun ρ : ℝ => ρ ^ D) (𝓝[<] 1) (𝓝 1) := by
      simpa using ((continuous_pow D).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    have hI : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ ∈ Set.Ioo r 1 := Ioo_mem_nhdsLT hr1
    obtain ⟨ρ, hρ1, hρ2⟩ := (hI.and (hlim.eventually (lt_mem_nhds hq1))).exists
    exact ⟨ρ, hρ1.1.le, hρ1.2, hρ2⟩
  have dom : ∀ ρ, ρ₀ ≤ ρ → ρ < 1 → ∀ k, k ≠ m → ‖a k‖ * ρ ^ k < M * ρ ^ m := by
    intro ρ h1 h2 k hk
    have hρ : 0 < ρ := hr0.trans_le (hρ₀r.trans h1)
    rcases lt_or_gt_of_ne hk with hk | hk
    · have hρk : 0 < ρ ^ k := zpow_pos hρ k
      have e : ρ ^ m = ρ ^ (m - k) * ρ ^ k := by rw [← zpow_add₀ hρ.ne']; congr 1; ring
      rw [e, ← mul_assoc]
      refine mul_lt_mul_of_pos_right ?_ hρk
      by_cases hkG : M * r ^ m ≤ ‖a k‖ * r ^ k
      · have hkB : B' ≤ k := hB' hkG
        have h3 : ρ ^ (D : ℤ) ≤ ρ ^ (m - k) :=
          zpow_le_zpow_right_of_le_one₀ hρ h2.le (by omega)
        have h4 : ρ₀ ^ D ≤ ρ ^ D := pow_le_pow_left₀ (hr0.le.trans hρ₀r) h1 D
        rw [zpow_natCast] at h3
        have h5 : ‖a k‖ ≤ q * M := by rw [← hmS]; exact hq _ _ (by rw [hmS]; exact hbelow k hk)
        nlinarith
      · have hrk : 0 < r ^ k := zpow_pos hr0 k
        have e' : r ^ m = r ^ (m - k) * r ^ k := by rw [← zpow_add₀ hr0.ne']; congr 1; ring
        rw [not_le, e', ← mul_assoc] at hkG
        have h6 : ‖a k‖ < M * r ^ (m - k) := lt_of_mul_lt_mul_right hkG hrk.le
        have h7 : r ^ (m - k) ≤ ρ ^ (m - k) :=
          zpow_le_zpow_left₀ (by omega) hr0.le (hρ₀r.trans h1)
        nlinarith
    · calc ‖a k‖ * ρ ^ k ≤ M * ρ ^ k := mul_le_mul_of_nonneg_right (hN k) (by positivity)
        _ < M * ρ ^ m := mul_lt_mul_of_pos_left (zpow_lt_zpow_right_of_lt_one₀ hρ h2 hk) hM

  set u : ℤ → K := fun n => if n = 0 then 0 else a (n + m) / a m
  have hweight : ∀ ρ, 0 < ρ → ∀ n, n ≠ 0 →
      ‖u n‖ * ρ ^ n = ‖a (n + m)‖ * ρ ^ (n + m) / (M * ρ ^ m) := by
    intro ρ hρ n hn
    simp only [u, if_neg hn, norm_div, hmS]
    rw [zpow_add₀ hρ.ne']
    field_simp
  have hu : ∀ ρ, ρ₀ ≤ ρ → ρ < 1 → ConvergesAt u ρ ∧ gaussNorm u ρ < 1 := by
    intro ρ h1 h2
    have hρ : 0 < ρ := hr0.trans_le (hρ₀r.trans h1)
    have ha : ConvergesAt a ρ := (hc ρ (hρ₀r.trans h1) h2).1
    have hshift : Tendsto (fun n : ℤ => ‖a (n + m)‖ * ρ ^ (n + m) / (M * ρ ^ m)) cofinite
        (𝓝 0) := by
      have := (ha.comp (add_left_injective m).tendsto_cofinite).div_const (M * ρ ^ m)
      simpa [Function.comp] using this
    have hconv : ConvergesAt u ρ := by
      refine squeeze_zero (fun n => by positivity) (fun n => ?_) hshift
      by_cases hn : n = 0
      · simp only [u, if_pos hn, norm_zero, zero_mul]; positivity
      · exact (hweight ρ hρ n hn).le
    refine ⟨hconv, ?_⟩
    by_cases hu0 : u = 0
    · rw [hu0]
      have : gaussNorm (0 : ℤ → K) ρ = 0 := by simp [gaussNorm]
      rw [this]; exact one_pos
    obtain ⟨n, hn⟩ := hconv.exists_eq_gaussNorm hρ hu0
    rw [← hn]
    by_cases hn0 : n = 0
    · simp only [u, if_pos hn0, norm_zero, zero_mul]; exact one_pos
    · rw [hweight ρ hρ n hn0, div_lt_one (by positivity)]
      exact dom ρ h1 h2 (n + m) (by omega)
  set U : Robba K := ⟨u, ⟨ρ₀, hρ₀1, fun ρ h1 h2 _ => (hu ρ h1 h2).1⟩⟩
  have hfU : f = single m (a m) * (1 + U) := by
    ext n
    rw [coeff_single_mul]
    show a n = a m * ((Pi.single 0 (1 : K) : ℤ → K) (n - m) + u (n - m))
    by_cases hn : n - m = 0
    · have : n = m := by omega
      subst this; simp [u]
    · simp only [u, Pi.single_apply, if_neg hn, zero_add, sub_add_cancel]
      field_simp
  rw [hfU]
  exact (isUnit_single m ham).mul (isUnit_one_add (hr0.trans_le hρ₀r) hρ₀1 hu)



end Robba

end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

namespace Laurent

variable {a b : ℤ → K} {ρ : ℝ}

def slopeMult (a : ℤ → K) (ρ : ℝ) : ℤ := highIndex a ρ - lowIndex a ρ

theorem zpow_rpow_comm {x : ℝ} (hx : 0 < x) (n : ℤ) (s : ℝ) : (x ^ s) ^ n = (x ^ n) ^ s := by
  rw [← Real.rpow_intCast, ← Real.rpow_intCast x n, ← Real.rpow_mul hx.le,
    ← Real.rpow_mul hx.le, mul_comm]

theorem weight_interp {ρ₁ ρ₂ t : ℝ} (h1 : 0 < ρ₁) (h2 : 0 < ρ₂) (n : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    x * (ρ₁ ^ (1 - t) * ρ₂ ^ t) ^ n = (x * ρ₁ ^ n) ^ (1 - t) * (x * ρ₂ ^ n) ^ t := by
  rw [mul_zpow, zpow_rpow_comm h1, zpow_rpow_comm h2, Real.mul_rpow hx (by positivity),
    Real.mul_rpow hx (by positivity)]
  have : x = x ^ (1 - t) * x ^ t := by
    rw [← Real.rpow_add' hx (by norm_num), sub_add_cancel, Real.rpow_one]
  conv_lhs => rw [this]
  ring

theorem gaussNorm_interp_le {ρ₁ ρ₂ t : ℝ} (h1 : 0 < ρ₁) (h2 : 0 < ρ₂) (hc1 : ConvergesAt a ρ₁)
    (hc2 : ConvergesAt a ρ₂) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    gaussNorm a (ρ₁ ^ (1 - t) * ρ₂ ^ t) ≤ gaussNorm a ρ₁ ^ (1 - t) * gaussNorm a ρ₂ ^ t :=
  gaussNorm_le fun n => by
    rw [weight_interp h1 h2 n (norm_nonneg _)]
    exact mul_le_mul (Real.rpow_le_rpow (by positivity) (hc1.le_gaussNorm n) (by linarith))
      (Real.rpow_le_rpow (by positivity) (hc2.le_gaussNorm n) ht0) (by positivity)
      (Real.rpow_nonneg (gaussNorm_nonneg h1) _)

theorem gaussNorm_le_max {ρ₁ ρ₂ : ℝ} (h1 : 0 < ρ₁) (hle1 : ρ₁ ≤ ρ) (hle2 : ρ ≤ ρ₂)
    (hc1 : ConvergesAt a ρ₁) (hc2 : ConvergesAt a ρ₂) :
    gaussNorm a ρ ≤ max (gaussNorm a ρ₁) (gaussNorm a ρ₂) := by
  have hρ : 0 < ρ := h1.trans_le hle1
  refine gaussNorm_le fun n => ?_
  rcases le_total 0 n with hn | hn
  · exact ((mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ hn hρ.le hle2) (norm_nonneg _)).trans
      (hc2.le_gaussNorm n)).trans (le_max_right _ _)
  · have h3 : ρ ^ n ≤ ρ₁ ^ n := by
      rw [show ρ ^ n = (ρ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv],
        show ρ₁ ^ n = (ρ₁ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]
      exact inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (neg_nonneg.2 hn) h1.le hle1)
    exact ((mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans (hc1.le_gaussNorm n)).trans
      (le_max_left _ _)

end Laurent

namespace Laurent

variable {a : ℤ → K} {α β : ℝ}

theorem lowIndex_mono {ρ ρ' : ℝ} (hρ : 0 < ρ) (hle : ρ ≤ ρ') (h : ConvergesAt a ρ)
    (h' : ConvergesAt a ρ') (ha : a ≠ 0) : lowIndex a ρ ≤ lowIndex a ρ' := by
  rcases hle.lt_or_eq with hlt | rfl
  · exact (lowIndex_le_highIndex hρ h ha).trans (highIndex_le_lowIndex hρ hlt h h' ha)
  · exact le_rfl

theorem highIndex_mono {ρ ρ' : ℝ} (hρ : 0 < ρ) (hle : ρ ≤ ρ') (h : ConvergesAt a ρ)
    (h' : ConvergesAt a ρ') (ha : a ≠ 0) : highIndex a ρ ≤ highIndex a ρ' := by
  rcases hle.lt_or_eq with hlt | rfl
  · exact (highIndex_le_lowIndex hρ hlt h h' ha).trans (lowIndex_le_highIndex (hρ.trans hlt) h' ha)
  · exact le_rfl

theorem exists_break (hα : 0 < α) (hαβ : α ≤ β) (hA : ConvergesAt a α) (hB : ConvergesAt a β)
    (ha : a ≠ 0) {n : ℤ} (hn1 : lowIndex a α ≤ n) (hn2 : n < highIndex a β) :
    ∃ σ ∈ Set.Icc α β, lowIndex a σ ≤ n ∧ n < highIndex a σ := by
  have hconv : ∀ σ ∈ Set.Icc α β, ConvergesAt a σ := fun σ hσ =>
    hA.of_le_of_le hB hα hσ.1 hσ.2
  have hpos : ∀ σ ∈ Set.Icc α β, 0 < σ := fun σ hσ => hα.trans_le hσ.1
  have hβ : 0 < β := hα.trans_le hαβ
  by_cases h1 : n < highIndex a α
  · exact ⟨α, ⟨le_rfl, hαβ⟩, hn1, h1⟩
  by_cases h2 : lowIndex a β ≤ n
  · exact ⟨β, ⟨hαβ, le_rfl⟩, h2, hn2⟩
  push_neg at h1 h2
  have hLα := lowIndex_le_highIndex hα hA ha
  have hLβ := lowIndex_le_highIndex hβ hB ha
  have hαβ' : α < β := by
    rcases hαβ.lt_or_eq with h | h
    · exact h
    · subst h; omega
  set C := Finset.Icc (lowIndex a α) (highIndex a β)
  set C1 := C.filter (· ≤ n)
  set C2 := C.filter (n < ·)
  have hC1 : highIndex a α ∈ C1 := by simp only [C1, C, Finset.mem_filter, Finset.mem_Icc]; omega
  have hC2 : lowIndex a β ∈ C2 := by simp only [C2, C, Finset.mem_filter, Finset.mem_Icc]; omega
  have ne1 : C1.Nonempty := ⟨_, hC1⟩
  have ne2 : C2.Nonempty := ⟨_, hC2⟩
  set A : ℝ → ℝ := fun σ => C1.sup' ne1 fun k => ‖a k‖ * σ ^ k
  set B : ℝ → ℝ := fun σ => C2.sup' ne2 fun k => ‖a k‖ * σ ^ k
  have hw : ∀ k : ℤ, ContinuousOn (fun σ : ℝ => ‖a k‖ * σ ^ k) (Set.Icc α β) := fun k =>
    continuousOn_const.mul ((continuousOn_zpow₀ k).mono fun σ hσ =>
      Set.mem_compl_singleton_iff.2 (hpos σ hσ).ne')
  have hcont : ContinuousOn (fun σ => A σ - B σ) (Set.Icc α β) :=
    (ContinuousOn.finset_sup'_apply ne1 fun k _ => hw k).sub
      (ContinuousOn.finset_sup'_apply ne2 fun k _ => hw k)
  have hAle : ∀ σ ∈ Set.Icc α β, A σ ≤ gaussNorm a σ := fun σ hσ =>
    Finset.sup'_le _ _ fun k _ => (hconv σ hσ).le_gaussNorm k
  have hBle : ∀ σ ∈ Set.Icc α β, B σ ≤ gaussNorm a σ := fun σ hσ =>
    Finset.sup'_le _ _ fun k _ => (hconv σ hσ).le_gaussNorm k
  have hgα : 0 < A α - B α := by
    have e1 : gaussNorm a α ≤ A α := by
      rw [← show ‖a (highIndex a α)‖ * α ^ highIndex a α = gaussNorm a α from
        highIndex_mem hα hA ha]
      exact Finset.le_sup' (fun k => ‖a k‖ * α ^ k) hC1
    have e2 : B α < gaussNorm a α := (Finset.sup'_lt_iff _).2 fun k hk => by
      simp only [C2, Finset.mem_filter] at hk
      exact weight_lt_of_highIndex_lt hα hA ha (by omega)
    linarith
  have hgβ : A β - B β < 0 := by
    have e1 : gaussNorm a β ≤ B β := by
      rw [← show ‖a (lowIndex a β)‖ * β ^ lowIndex a β = gaussNorm a β from
        lowIndex_mem hβ hB ha]
      exact Finset.le_sup' (fun k => ‖a k‖ * β ^ k) hC2
    have e2 : A β < gaussNorm a β := (Finset.sup'_lt_iff _).2 fun k hk => by
      simp only [C1, Finset.mem_filter] at hk
      exact weight_lt_of_lt_lowIndex hβ hB ha (by omega)
    linarith
  obtain ⟨σ, hσ, hgσ⟩ := intermediate_value_Icc' hαβ hcont ⟨hgβ.le, hgα.le⟩
  simp only at hgσ
  have hσα : α < σ := lt_of_le_of_ne hσ.1 fun h => by subst h; linarith
  have hσβ : σ < β := lt_of_le_of_ne hσ.2 fun h => by subst h; linarith
  have hσ0 := hpos σ hσ
  have hcσ := hconv σ hσ
  have i1 := highIndex_le_lowIndex hα hσα hA hcσ ha
  have i2 := highIndex_le_lowIndex hσ0 hσβ hcσ hB ha
  have i3 := lowIndex_le_highIndex hσ0 hcσ ha
  have hLmem := lowIndex_mem hσ0 hcσ ha
  have hgauss : gaussNorm a σ ≤ max (A σ) (B σ) := by
    rw [← show ‖a (lowIndex a σ)‖ * σ ^ lowIndex a σ = gaussNorm a σ from hLmem]
    by_cases hk : lowIndex a σ ≤ n
    · exact (Finset.le_sup' (fun k => ‖a k‖ * σ ^ k) (s := C1)
        (by simp only [C1, C, Finset.mem_filter, Finset.mem_Icc]; omega)).trans (le_max_left _ _)
    · exact (Finset.le_sup' (fun k => ‖a k‖ * σ ^ k) (s := C2)
        (by simp only [C2, C, Finset.mem_filter, Finset.mem_Icc]; omega)).trans (le_max_right _ _)
  have hAσ : A σ = gaussNorm a σ := by
    have := hAle σ hσ; have := hBle σ hσ
    rcases le_total (A σ) (B σ) with h | h
    · rw [max_eq_right h] at hgauss; linarith
    · rw [max_eq_left h] at hgauss; linarith
  have hBσ : B σ = gaussNorm a σ := by linarith
  obtain ⟨k1, hk1, hk1e⟩ := Finset.exists_mem_eq_sup' ne1 fun k => ‖a k‖ * σ ^ k
  obtain ⟨k2, hk2, hk2e⟩ := Finset.exists_mem_eq_sup' ne2 fun k => ‖a k‖ * σ ^ k
  have d1 : k1 ∈ domSet a σ := by
    show ‖a k1‖ * σ ^ k1 = gaussNorm a σ
    rw [← hk1e]; exact hAσ
  have d2 : k2 ∈ domSet a σ := by
    show ‖a k2‖ * σ ^ k2 = gaussNorm a σ
    rw [← hk2e]; exact hBσ
  simp only [C1, C2, Finset.mem_filter] at hk1 hk2
  exact ⟨σ, hσ, (lowIndex_le hσ0 hcσ ha d1).trans hk1.2,
    lt_of_lt_of_le hk2.2 (le_highIndex hσ0 hcσ ha d2)⟩

def breaks (a : ℤ → K) (α β : ℝ) : Set ℝ :=
  {ρ | ρ ∈ Set.Icc α β ∧ lowIndex a ρ < highIndex a ρ}

section Finite

variable (hα : 0 < α) (hαβ : α ≤ β) (hA : ConvergesAt a α) (hB : ConvergesAt a β) (ha : a ≠ 0)
include hα hαβ hA hB ha

theorem mem_Icc_indices {ρ : ℝ} (hρ : ρ ∈ Set.Icc α β) :
    lowIndex a α ≤ lowIndex a ρ ∧ highIndex a ρ ≤ highIndex a β := by
  have hc := hA.of_le_of_le hB hα hρ.1 hρ.2
  exact ⟨lowIndex_mono hα hρ.1 hA hc ha, highIndex_mono (hα.trans_le hρ.1) hρ.2 hc hB ha⟩

theorem breaks_finite : (breaks a α β).Finite := by
  refine Set.Finite.of_finite_image (f := fun ρ => lowIndex a ρ)
    ((Set.finite_Icc (lowIndex a α) (highIndex a β)).subset ?_) ?_
  · rintro _ ⟨ρ, hρ, rfl⟩
    have := mem_Icc_indices hα hαβ hA hB ha hρ.1
    exact ⟨this.1, hρ.2.le.trans this.2⟩
  · intro ρ hρ ρ' hρ' he
    simp only at he
    have hc := hA.of_le_of_le hB hα hρ.1.1 hρ.1.2
    have hc' := hA.of_le_of_le hB hα hρ'.1.1 hρ'.1.2
    rcases lt_trichotomy ρ ρ' with h | h | h
    · have := highIndex_le_lowIndex (hα.trans_le hρ.1.1) h hc hc' ha
      have := hρ.2
      omega
    · exact h
    · have := highIndex_le_lowIndex (hα.trans_le hρ'.1.1) h hc' hc ha
      have := hρ'.2
      omega

theorem sum_slopeMult_breaks :
    ∑ ρ ∈ (breaks_finite hα hαβ hA hB ha).toFinset, slopeMult a ρ =
      highIndex a β - lowIndex a α := by
  classical
  set s := (breaks_finite hα hαβ hA hB ha).toFinset
  set I : ℝ → Finset ℤ := fun ρ => Finset.Ico (lowIndex a ρ) (highIndex a ρ)
  have hmem : ∀ ρ, ρ ∈ s ↔ ρ ∈ breaks a α β := fun ρ => Set.Finite.mem_toFinset _
  have hdisj : (s : Set ℝ).PairwiseDisjoint I := by
    intro ρ hρ ρ' hρ' hne
    rw [Finset.mem_coe, hmem] at hρ hρ'
    have hc := hA.of_le_of_le hB hα hρ.1.1 hρ.1.2
    have hc' := hA.of_le_of_le hB hα hρ'.1.1 hρ'.1.2
    show Disjoint (I ρ) (I ρ')
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [I, Finset.mem_Ico] at hk hk'
    rcases lt_or_gt_of_ne hne with h | h
    · have := highIndex_le_lowIndex (hα.trans_le hρ.1.1) h hc hc' ha
      omega
    · have := highIndex_le_lowIndex (hα.trans_le hρ'.1.1) h hc' hc ha
      omega
  have hLH : lowIndex a α ≤ highIndex a β :=
    (lowIndex_le_highIndex hα hA ha).trans (highIndex_mono hα hαβ hA hB ha)
  have hunion : s.biUnion I = Finset.Ico (lowIndex a α) (highIndex a β) := by
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_Ico, hmem, I]
    constructor
    · rintro ⟨ρ, hρ, hk1, hk2⟩
      have := mem_Icc_indices hα hαβ hA hB ha hρ.1
      omega
    · rintro ⟨hk1, hk2⟩
      obtain ⟨σ, hσ, h1, h2⟩ := exists_break hα hαβ hA hB ha hk1 hk2
      exact ⟨σ, ⟨hσ, by omega⟩, h1, h2⟩
  have hcard := Finset.card_biUnion hdisj
  rw [hunion, Int.card_Ico] at hcard
  have : ∑ ρ ∈ s, slopeMult a ρ = ∑ ρ ∈ s, ((I ρ).card : ℤ) := Finset.sum_congr rfl fun ρ hρ => by
    rw [hmem] at hρ
    simp only [I, Int.card_Ico, slopeMult]
    have := hρ.2
    omega
  rw [this, ← Nat.cast_sum, ← hcard]
  omega

end Finite

end Laurent

namespace Robba

variable [CompleteSpace K]

end Robba

end GroundTheory.PAdicHodge
end
end
