import Mathlib
import GroundTheory.PAdicHodge.ThetaBDeRhamPlusFieldCycloUnitBdRZpow
import GroundTheory.PAdicHodge.TateCpTwist
import GroundTheory.PAdicHodge.AxLemma
import GroundTheory.PAdicHodge.CyclotomicField
import GroundTheory.PAdicHodge.NormalizedTraceClosure
import GroundTheory.PAdicHodge.CyclotomicTower
import GroundTheory.PAdicHodge.Admissible

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Polynomial Module

noncomputable section

variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def cyclotomicLayer (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) := K ⊔ cycl p n

def cyclotomicLimit : IntermediateField ℚ_[p] (PadicAlgCl p) := ⨆ n, cyclotomicLayer K n

theorem cyclotomicLayer_mono : Monotone (cyclotomicLayer K) := fun _ _ h =>
  sup_le_sup_left (cycl_mono h) K

theorem le_cyclotomicLayer (n : ℕ) : K ≤ cyclotomicLayer K n := le_sup_left

theorem cycl_le_cyclotomicLayer (n : ℕ) : cycl p n ≤ cyclotomicLayer K n := le_sup_right

theorem cyclotomicLayer_le_cyclotomicLimit (n : ℕ) : cyclotomicLayer K n ≤ cyclotomicLimit K :=
  le_iSup (cyclotomicLayer K) n

theorem mem_cyclotomicLimit {x : PadicAlgCl p} :
    x ∈ cyclotomicLimit K ↔ ∃ n, x ∈ cyclotomicLayer K n := by
  rw [← SetLike.mem_coe, cyclotomicLimit,
    coe_iSup_of_directed (cyclotomicLayer_mono K).directed_le, Set.mem_iUnion]
  rfl

theorem cyclotomicLayer_sup_cycl {n m : ℕ} (h : n ≤ m) :
    cyclotomicLayer K n ⊔ cycl p m = cyclotomicLayer K m := by
  rw [cyclotomicLayer, cyclotomicLayer, sup_assoc, sup_eq_right.2 (cycl_mono h)]

instance charZero_intermediateField (k : IntermediateField ℚ_[p] (PadicAlgCl p)) : CharZero k :=
  (algebraMap k (PadicAlgCl p)).charZero

variable [FiniteDimensional ℚ_[p] K]

instance finiteDimensional_cyclotomicLayer (n : ℕ) :
    FiniteDimensional ℚ_[p] (cyclotomicLayer K n) := by
  unfold cyclotomicLayer; infer_instance

def relDeg (n : ℕ) : ℕ := finrank (cycl p n) (extendScalars (cycl_le_cyclotomicLayer K n))

theorem finrank_cyclotomicLayer (n : ℕ) :
    finrank ℚ_[p] (cyclotomicLayer K n) = finrank ℚ_[p] (cycl p n) * relDeg K n :=
  finrank_eq_mul_finrank_extendScalars (cycl_le_cyclotomicLayer K n)

theorem relDeg_antitone : Antitone (relDeg K) := by
  intro n m h
  have c := finrank_sup_mul_le (k := cycl p n) (X := cyclotomicLayer K n) (Y := cycl p m)
    (cycl_le_cyclotomicLayer K n) (cycl_mono h)
  rw [cyclotomicLayer_sup_cycl K h, finrank_cyclotomicLayer, finrank_cyclotomicLayer] at c
  have pn : 0 < finrank ℚ_[p] (cycl p n) := Module.finrank_pos
  have pm : 0 < finrank ℚ_[p] (cycl p m) := Module.finrank_pos
  have : finrank ℚ_[p] (cycl p m) * finrank ℚ_[p] (cycl p n) * relDeg K m ≤
      finrank ℚ_[p] (cycl p m) * finrank ℚ_[p] (cycl p n) * relDeg K n := by
    calc _ = finrank ℚ_[p] (cycl p m) * relDeg K m * finrank ℚ_[p] (cycl p n) := by ring
      _ ≤ _ := c
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left this (Nat.mul_pos pm pn)

theorem exists_relDeg_stable : ∃ N, 2 ≤ N ∧ ∀ m, N ≤ m → relDeg K m = relDeg K N := by
  classical
  have hex : ∃ v, ∃ n, relDeg K n = v := ⟨_, 0, rfl⟩
  obtain ⟨n₀, hn₀⟩ := Nat.find_spec hex
  have hmin : ∀ m, relDeg K n₀ ≤ relDeg K m := fun m => hn₀ ▸ Nat.find_min' hex ⟨m, rfl⟩
  refine ⟨max n₀ 2, le_max_right _ _, fun m hm => le_antisymm (relDeg_antitone K hm) ?_⟩
  exact (relDeg_antitone K (le_max_left n₀ 2)).trans (hmin m)

def stableIndex : ℕ := Classical.choose (exists_relDeg_stable K)

theorem two_le_stableIndex : 2 ≤ stableIndex K := (Classical.choose_spec (exists_relDeg_stable K)).1

theorem relDeg_eq_of_le {m : ℕ} (h : stableIndex K ≤ m) : relDeg K m = relDeg K (stableIndex K) :=
  (Classical.choose_spec (exists_relDeg_stable K)).2 m h

theorem finrank_linearDisjoint {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m) :
    finrank ℚ_[p] (cyclotomicLayer K m) * finrank ℚ_[p] (cycl p n) =
      finrank ℚ_[p] (cyclotomicLayer K n) * finrank ℚ_[p] (cycl p m) := by
  rw [finrank_cyclotomicLayer, finrank_cyclotomicLayer, relDeg_eq_of_le K hn,
    relDeg_eq_of_le K (hn.trans hnm)]
  ring

theorem normTrace_cycl_eq_of_mem {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m)
    {z : PadicAlgCl p} (hz : z ∈ cyclotomicLayer K n) :
    normTrace (cycl p m) z = normTrace (cycl p n) z := by
  refine normTrace_eq_of_finrank_sup (cycl_le_cyclotomicLayer K n) (cycl_mono hnm) ?_ hz
  rw [cyclotomicLayer_sup_cycl K hnm]
  exact finrank_linearDisjoint K hn hnm

theorem normTrace_cyclotomicLayer_eq_of_mem {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m)
    {a : PadicAlgCl p} (ha : a ∈ cycl p m) :
    normTrace (cyclotomicLayer K n) a = normTrace (cycl p n) a := by
  refine normTrace_eq_of_finrank_sup (cycl_mono hnm) (cycl_le_cyclotomicLayer K n) ?_ ha
  rw [sup_comm, cyclotomicLayer_sup_cycl K hnm, finrank_linearDisjoint K hn hnm]
  ring

theorem finiteDimensional_extendScalars {k E : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : k ≤ E)
    [FiniteDimensional ℚ_[p] E] : FiniteDimensional k (extendScalars h) := by
  apply Module.finite_of_finrank_pos
  have hE : 0 < finrank ℚ_[p] E := Module.finrank_pos
  rw [finrank_eq_mul_finrank_extendScalars h] at hE
  exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at hE

instance finiteDimensional_cyclotomicLayer_cycl (n : ℕ) :
    FiniteDimensional (cycl p n) (extendScalars (cycl_le_cyclotomicLayer K n)) :=
  finiteDimensional_extendScalars _

theorem relDeg_pos (n : ℕ) : 0 < relDeg K n := Module.finrank_pos

def traceBasis : Basis (Fin (relDeg K (stableIndex K))) (cycl p (stableIndex K))
    (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K))) :=
  Module.finBasis _ _

def traceDualBasis : Basis (Fin (relDeg K (stableIndex K))) (cycl p (stableIndex K))
    (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K))) :=
  (Algebra.traceForm _ _).dualBasis (traceForm_nondegenerate _ _) (traceBasis K)

def towerVec (i : Fin (relDeg K (stableIndex K))) : PadicAlgCl p := (traceBasis K i : PadicAlgCl p)

def towerDualVec (i : Fin (relDeg K (stableIndex K))) : PadicAlgCl p :=
  (traceDualBasis K i : PadicAlgCl p)

theorem towerVec_mem (i : Fin (relDeg K (stableIndex K))) :
    towerVec K i ∈ cyclotomicLayer K (stableIndex K) :=
  (traceBasis K i).2

theorem towerDualVec_mem (i : Fin (relDeg K (stableIndex K))) :
    towerDualVec K i ∈ cyclotomicLayer K (stableIndex K) :=
  (traceDualBasis K i).2

theorem normTrace_towerVec_mul (i j : Fin (relDeg K (stableIndex K))) :
    normTrace (cycl p (stableIndex K)) (towerVec K i * towerDualVec K j) =
      if i = j then ((relDeg K (stableIndex K) : PadicAlgCl p))⁻¹ else 0 := by
  have e := normTraceF_eq_trace_div (cycl p (stableIndex K)) (Ω := PadicAlgCl p)
    (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K))) (traceBasis K i * traceDualBasis K j)
  have ht : Algebra.trace (cycl p (stableIndex K)) (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K)))
      (traceBasis K i * traceDualBasis K j) = if i = j then 1 else 0 := by
    rw [mul_comm, ← Algebra.traceForm_apply, traceDualBasis,
      LinearMap.BilinForm.apply_dualBasis_left]
  rw [ht] at e
  rw [normTrace]
  change algebraMap _ _ (normTraceF _ (algebraMap (extendScalars (cycl_le_cyclotomicLayer K
    (stableIndex K))) (PadicAlgCl p) (traceBasis K i * traceDualBasis K j))) = _
  rw [e]
  split_ifs <;> simp [relDeg]

def towerCoeff (m : ℕ) (y : PadicAlgCl p) (i : Fin (relDeg K (stableIndex K))) : PadicAlgCl p :=
  (relDeg K (stableIndex K) : PadicAlgCl p) * normTrace (cycl p m) (y * towerDualVec K i)

theorem towerCoeff_mem (m : ℕ) (y : PadicAlgCl p) (i : Fin (relDeg K (stableIndex K))) :
    towerCoeff K m y i ∈ cycl p m :=
  mul_mem (IntermediateField.natCast_mem _ _) (normTrace_mem _ _)

theorem normTrace_sum_towerVec_mul {m : ℕ} (hm : stableIndex K ≤ m)
    (c : Fin (relDeg K (stableIndex K)) → PadicAlgCl p) (hc : ∀ i, c i ∈ cycl p m)
    (j : Fin (relDeg K (stableIndex K))) :
    normTrace (cycl p m) ((∑ i, c i * towerVec K i) * towerDualVec K j) =
      c j / (relDeg K (stableIndex K) : PadicAlgCl p) := by
  rw [Finset.sum_mul, normTrace_sum]
  have : ∀ i ∈ (Finset.univ : Finset (Fin (relDeg K (stableIndex K)))),
      normTrace (cycl p m) (c i * towerVec K i * towerDualVec K j) =
        c i * (if i = j then ((relDeg K (stableIndex K) : PadicAlgCl p))⁻¹ else 0) := by
    intro i _
    rw [mul_assoc, normTrace_mul_of_mem _ (hc i),
      normTrace_cycl_eq_of_mem K le_rfl hm (mul_mem (towerVec_mem K i) (towerDualVec_mem K j)),
      normTrace_towerVec_mul]
  rw [Finset.sum_congr rfl this]
  simp [div_eq_mul_inv]

theorem eq_sum_towerCoeff {m : ℕ} (hm : stableIndex K ≤ m) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLayer K m) : y = ∑ i, towerCoeff K m y i * towerVec K i := by
  set d := relDeg K (stableIndex K)
  let L := extendScalars (cycl_le_cyclotomicLayer K m)
  have hv : ∀ i, towerVec K i ∈ L := fun i => cyclotomicLayer_mono K hm (towerVec_mem K i)
  let v : Fin d → L := fun i => ⟨towerVec K i, hv i⟩
  have hd0 : (d : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 (relDeg_pos K _).ne'
  have hli : LinearIndependent (cycl p m) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 : (∑ i, (g i : PadicAlgCl p) * towerVec K i) = 0 := by
      have := congrArg (fun x : L => (x : PadicAlgCl p)) hg
      simpa [v, Algebra.smul_def] using this
    have h2 := normTrace_sum_towerVec_mul K hm (fun i => (g i : PadicAlgCl p)) (fun i => (g i).2) j
    rw [h1, zero_mul, normTrace_zero, eq_comm, div_eq_zero_iff] at h2
    exact Subtype.ext (h2.resolve_right hd0)
  have hcard : Fintype.card (Fin d) = finrank (cycl p m) L := by
    rw [Fintype.card_fin]
    exact (relDeg_eq_of_le K hm).symm
  haveI : Nonempty (Fin d) := ⟨⟨0, relDeg_pos K _⟩⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hsum := B.sum_repr ⟨y, hy⟩
  have hyexp : y = ∑ i, ((B.repr ⟨y, hy⟩ i : cycl p m) : PadicAlgCl p) * towerVec K i := by
    have := congrArg (fun x : L => (x : PadicAlgCl p)) hsum
    simpa [B, v, Algebra.smul_def] using this.symm
  have hc : ∀ j, ((B.repr ⟨y, hy⟩ j : cycl p m) : PadicAlgCl p) = towerCoeff K m y j := by
    intro j
    have := normTrace_sum_towerVec_mul K hm _ (fun i => (B.repr ⟨y, hy⟩ i).2) j
    rw [← hyexp] at this
    rw [towerCoeff, this]
    exact (mul_div_cancel₀ _ hd0).symm
  conv_lhs => rw [hyexp]
  simp_rw [hc]
  rfl

theorem norm_towerCoeff_le {m : ℕ} (hm : stableIndex K ≤ m) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLayer K m) (i : Fin (relDeg K (stableIndex K))) :
    ‖towerCoeff K m y i‖ ≤ ‖y * towerDualVec K i‖ := by
  let L := extendScalars (cycl_le_cyclotomicLayer K m)
  have hw : y * towerDualVec K i ∈ L :=
    mul_mem hy (cyclotomicLayer_mono K hm (towerDualVec_mem K i))
  apply norm_natCast_mul_normTrace_le
  have e := minpoly.algebraMap_eq (A := cycl p m) (algebraMap L (PadicAlgCl p)).injective
    (⟨y * towerDualVec K i, hw⟩ : L)
  change (minpoly (cycl p m) (algebraMap L (PadicAlgCl p) ⟨_, hw⟩)).natDegree ∣ _
  rw [e, ← relDeg_eq_of_le K hm]
  exact minpoly.degree_dvd (IsIntegral.of_finite _ _)

theorem norm_normTrace_cyclotomicLayer_le {cF : ℝ} (hcF : 0 ≤ cF)
    (hF : ∀ n m : ℕ, stableIndex K ≤ n → n ≤ m → ∀ x ∈ cycl p m,
      ‖normTrace (cycl p n) x‖ ≤ cF * ‖x‖)
    {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLayer K m) :
    ‖normTrace (cyclotomicLayer K n) y‖ ≤
      cF * (∑ i, ‖towerVec K i‖ * ‖towerDualVec K i‖) * ‖y‖ := by
  have hexp := eq_sum_towerCoeff K (hn.trans hnm) hy
  have key : normTrace (cyclotomicLayer K n) y =
      ∑ i, towerVec K i * normTrace (cycl p n) (towerCoeff K m y i) := by
    conv_lhs => rw [hexp]
    rw [normTrace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, normTrace_mul_of_mem _ (cyclotomicLayer_mono K hn (towerVec_mem K i)),
      normTrace_cyclotomicLayer_eq_of_mem K hn hnm (towerCoeff_mem K m y i)]
  rw [key, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have h1 := hF n m hn hnm _ (towerCoeff_mem K m y i)
  have h2 := norm_towerCoeff_le K (hn.trans hnm) hy i
  rw [norm_mul] at h2
  calc ‖towerVec K i‖ * ‖normTrace (cycl p n) (towerCoeff K m y i)‖
      ≤ ‖towerVec K i‖ * (cF * ‖towerCoeff K m y i‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ ‖towerVec K i‖ * (cF * (‖y‖ * ‖towerDualVec K i‖)) := by gcongr
    _ = cF * (‖towerVec K i‖ * ‖towerDualVec K i‖) * ‖y‖ := by ring

omit [FiniteDimensional ℚ_[p] K] in

theorem cyclotomicLayer_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : ∀ x ∈ K, σ x = x)
    (n : ℕ) :
    (cyclotomicLayer K n).map (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) = cyclotomicLayer K n := by
  rw [cyclotomicLayer, IntermediateField.map_sup, cycl_map]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change σ y ∈ K
    rw [hσ y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, hσ x hx⟩

omit [FiniteDimensional ℚ_[p] K] in
theorem map_mem_cyclotomicLayer (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x ∈ K, σ x = x) {n : ℕ} {x : PadicAlgCl p} (hx : x ∈ cyclotomicLayer K n) :
    σ x ∈ cyclotomicLayer K n := by
  rw [← cyclotomicLayer_map K σ hσ n]
  exact ⟨x, hx, rfl⟩

omit [FiniteDimensional ℚ_[p] K] in
theorem map_mem_cyclotomicLimit (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x ∈ K, σ x = x) {x : PadicAlgCl p} (hx : x ∈ cyclotomicLimit K) :
    σ x ∈ cyclotomicLimit K := by
  obtain ⟨n, hn⟩ := (mem_cyclotomicLimit K).1 hx
  exact (mem_cyclotomicLimit K).2 ⟨n, map_mem_cyclotomicLayer K σ hσ hn⟩

omit [FiniteDimensional ℚ_[p] K] in

theorem normTrace_cyclotomicLayer_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : ∀ x ∈ K, σ x = x) (n : ℕ) (y : PadicAlgCl p) :
    normTrace (cyclotomicLayer K n) (σ y) = σ (normTrace (cyclotomicLayer K n) y) :=
  normTrace_map_of_map_eq _ σ (cyclotomicLayer_map K σ hσ n) y

omit [FiniteDimensional ℚ_[p] K] in

theorem normTrace_cyclotomicLayer_gal (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    normTrace (cyclotomicLayer K n) (σ y) = σ (normTrace (cyclotomicLayer K n) y) :=
  normTrace_cyclotomicLayer_map K (σ.restrictScalars ℚ_[p]) (fun x hx => σ.commutes ⟨x, hx⟩) n y

section Gamma

variable {n : ℕ} (γ : Gal(PadicAlgCl p/cyclotomicLayer K n))

end Gamma

end

end GroundTheory.PAdicHodge
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Module Set

noncomputable section

variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]

def tateTrace (n : ℕ) : PadicAlgCl p → PadicAlgCl p := normTrace (cyclotomicLayer K n)

theorem tateTrace_add (n : ℕ) (y z : PadicAlgCl p) :
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  normTrace_add _ y z

theorem tateTrace_mem (n : ℕ) (y : PadicAlgCl p) : tateTrace K n y ∈ cyclotomicLayer K n :=
  normTrace_mem _ y

theorem tateTrace_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTrace K n a = a :=
  normTrace_of_mem _ ha

theorem tateTrace_mul_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n)
    (y : PadicAlgCl p) : tateTrace K n (a * y) = a * tateTrace K n y :=
  normTrace_mul_of_mem _ ha y

theorem tateTrace_gal (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p) :
    tateTrace K n (σ y) = σ (tateTrace K n y) :=
  normTrace_cyclotomicLayer_gal K σ n y

theorem tateTrace_tateTrace_of_le {n n' : ℕ} (h : n ≤ n') (y : PadicAlgCl p) :
    tateTrace K n (tateTrace K n' y) = tateTrace K n y :=
  normTrace_normTrace_of_le (cyclotomicLayer_mono K h) y

theorem exists_norm_tateTrace_le_of_stableIndex_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, stableIndex K ≤ n → ∀ x ∈ cyclotomicLimit K,
      ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  refine ⟨p * ∑ i, ‖towerVec K i‖ * ‖towerDualVec K i‖,
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => by positivity), ?_⟩
  intro n hn x hx
  obtain ⟨m, hm⟩ := (mem_cyclotomicLimit K).1 hx
  have hm' : x ∈ cyclotomicLayer K (max m n) := cyclotomicLayer_mono K (le_max_left m n) hm
  refine norm_normTrace_cyclotomicLayer_le K (Nat.cast_nonneg p) ?_ hn (le_max_right m n) hm'
  intro n' m' hn' hnm' y hy
  exact norm_normTrace_cycl_le
    (le_trans (by norm_num) ((two_le_stableIndex K).trans hn')) hnm' hy

theorem exists_norm_tateTrace_le_on_layer (n N : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ cyclotomicLayer K N, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  let S : Submodule ℚ_[p] (PadicAlgCl p) := (cyclotomicLayer K N).toSubalgebra.toSubmodule
  haveI : FiniteDimensional ℚ_[p] S :=
    inferInstanceAs (FiniteDimensional ℚ_[p] (cyclotomicLayer K N))
  let f : S →ₗ[ℚ_[p]] PadicAlgCl p :=
    ((normTraceₗ (cyclotomicLayer K n)).restrictScalars ℚ_[p]).comp S.subtype
  let f' := LinearMap.toContinuousLinearMap f
  refine ⟨‖f'‖, ContinuousLinearMap.opNorm_nonneg f', fun x hx => ?_⟩
  have := f'.le_opNorm ⟨x, hx⟩
  exact this

theorem exists_norm_tateTrace_le :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n, ∀ x ∈ cyclotomicLimit K, ‖tateTrace K n x‖ ≤ c * ‖x‖ := by
  obtain ⟨c, hc0, hc⟩ := exists_norm_tateTrace_le_of_stableIndex_le K
  choose c' hc'0 hc' using fun n => exists_norm_tateTrace_le_on_layer K n (stableIndex K)
  refine ⟨c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n), by
    have : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
    positivity, ?_⟩
  intro n x hx
  have hs : 0 ≤ ∑ n ∈ Finset.range (stableIndex K), c' n := Finset.sum_nonneg fun n _ => hc'0 n
  by_cases hn : stableIndex K ≤ n
  · calc ‖tateTrace K n x‖ ≤ c * ‖x‖ := hc n hn x hx
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        nlinarith [mul_nonneg (mul_nonneg hc0 hs) (norm_nonneg x)]
  · push_neg at hn
    have hle : c' n ≤ ∑ n ∈ Finset.range (stableIndex K), c' n :=
      Finset.single_le_sum (fun n _ => hc'0 n) (Finset.mem_range.2 hn)
    rw [← tateTrace_tateTrace_of_le K hn.le x]
    calc ‖tateTrace K n (tateTrace K (stableIndex K) x)‖
        ≤ c' n * ‖tateTrace K (stableIndex K) x‖ := hc' n _ (tateTrace_mem K _ x)
      _ ≤ c' n * (c * ‖x‖) := mul_le_mul_of_nonneg_left (hc _ le_rfl x hx) (hc'0 n)
      _ ≤ c * (1 + ∑ n ∈ Finset.range (stableIndex K), c' n) * ‖x‖ := by
        have := norm_nonneg x
        nlinarith [mul_nonneg hc0 this]

def tateBound : ℝ := Classical.choose (exists_norm_tateTrace_le K)

theorem tateBound_nonneg : 0 ≤ tateBound K := (Classical.choose_spec (exists_norm_tateTrace_le K)).1

theorem norm_tateTrace_le (n : ℕ) {x : PadicAlgCl p} (hx : x ∈ cyclotomicLimit K) :
    ‖tateTrace K n x‖ ≤ tateBound K * ‖x‖ :=
  (Classical.choose_spec (exists_norm_tateTrace_le K)).2 n x hx

section Completion

def cyclotomicCompletion : Set ℂ_[p] := closureInCp (cyclotomicLimit K)

def tateTraceHat (n : ℕ) : ℂ_[p] → ℂ_[p] := extendToClosure (cyclotomicLimit K) (tateTrace K n)

variable {K}

theorem tateTrace_add_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K, ∀ z ∈ cyclotomicLimit K,
    tateTrace K n (y + z) = tateTrace K n y + tateTrace K n z :=
  fun y _ z _ => tateTrace_add K n y z

theorem norm_tateTrace_le_of_mem (n : ℕ) : ∀ y ∈ cyclotomicLimit K,
    ‖tateTrace K n y‖ ≤ tateBound K * ‖y‖ :=
  fun _ hy => norm_tateTrace_le K n hy

theorem norm_tateTraceHat_le (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    ‖tateTraceHat K n x‖ ≤ tateBound K * ‖x‖ :=
  norm_extendToClosure_le (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx

theorem tateTraceHat_add (n : ℕ) {x x' : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K)
    (hx' : x' ∈ cyclotomicCompletion K) :
    tateTraceHat K n (x + x') = tateTraceHat K n x + tateTraceHat K n x' :=
  (extendToClosure_add (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) hx hx').2

theorem tateTraceHat_mem (n : ℕ) {x : ℂ_[p]} (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n x ∈
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (cyclotomicLayer K n : Set (PadicAlgCl p)) :=
  extendToClosure_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (fun y _ => tateTrace_mem K n y) hx

theorem tateTraceHat_coe_of_mem {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) :
    tateTraceHat K n (a : ℂ_[p]) = a :=
  extendToClosure_coe_of_mem (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha => tateTrace_of_mem K ha) ha

theorem tateTraceHat_mul {n : ℕ} {a : PadicAlgCl p} (ha : a ∈ cyclotomicLayer K n) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) :
    tateTraceHat K n ((a : ℂ_[p]) * x) = (a : ℂ_[p]) * tateTraceHat K n x :=
  extendToClosure_mul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n)
    (cyclotomicLayer_le_cyclotomicLimit K n) (fun a ha y _ => tateTrace_mul_of_mem K ha y) ha hx

theorem gal_mem_cyclotomicLimit (σ : Gal(PadicAlgCl p/K)) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLimit K) : σ y ∈ cyclotomicLimit K :=
  map_mem_cyclotomicLimit K (σ.restrictScalars ℚ_[p]) (fun x hx => σ.commutes ⟨x, hx⟩) hy

theorem smul_mem_cyclotomicCompletion (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : σ • x ∈ cyclotomicCompletion K :=
  smul_mem_closureInCp σ (fun _ hy => gal_mem_cyclotomicLimit σ hy) hx

theorem tateTraceHat_smul (n : ℕ) (σ : Gal(PadicAlgCl p/K)) {x : ℂ_[p]}
    (hx : x ∈ cyclotomicCompletion K) : tateTraceHat K n (σ • x) = σ • tateTraceHat K n x :=
  extendToClosure_smul (tateTrace_add_of_mem n) (norm_tateTrace_le_of_mem n) σ
    (fun _ hy => gal_mem_cyclotomicLimit σ hy) (fun y _ => tateTrace_gal K σ n y) hx

end Completion

section Gamma

variable {K}

end Gamma

end

end GroundTheory.PAdicHodge
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField UniformSpace

variable {p : ℕ} [hp : Fact p.Prime]

section Torsion

theorem one_add_pow_ne_one {w : PadicAlgCl p} (hw0 : w ≠ 0) (hw : ‖w‖ < (p : ℝ)⁻¹) {m : ℕ}
    (hm : m ≠ 0) : (1 + w) ^ m ≠ 1 := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  have hexp : (1 + w) ^ (m' + 1) - 1 = ((m' + 1 : ℕ) : PadicAlgCl p) * w +
      ∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p) := by
    rw [add_comm (1 : PadicAlgCl p) w, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, pow_one,
      Nat.choose_one_right, zero_add]
    ring
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hmpos : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ := by
    rw [norm_pos_iff]; exact_mod_cast Nat.succ_ne_zero m'
  have hlead : 0 < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    rw [norm_mul]; exact mul_pos hmpos hwpos

  have hterm : ∀ k ∈ Finset.range m', ‖w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
      < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    intro k _

    have hch : ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p) * ((k + 1 + 1 : ℕ) : PadicAlgCl p) =
        ((m' + 1 : ℕ) : PadicAlgCl p) * (m'.choose (k + 1) : PadicAlgCl p) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq m' (k + 1)).symm
    have hk0 : (k + 1 + 1 : ℕ) ≠ 0 := by omega
    have hknorm : ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤ ‖((k + 1 + 1 : ℕ) : PadicAlgCl p)‖ := by
      rw [norm_natCast_padicAlgCl hk0, zpow_neg, zpow_natCast]
      gcongr
      exact_mod_cast Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    have hkpos : (0 : ℝ) < ((k + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have hC : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ ≤
        ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ) := by
      have h1 := congrArg norm hch
      rw [norm_mul, norm_mul] at h1
      have h2 : ‖(m'.choose (k + 1) : PadicAlgCl p)‖ ≤ 1 :=
        IsUltrametricDist.norm_natCast_le_one (PadicAlgCl p) _
      have h3 : ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)⁻¹ ≤
          ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ := by
        calc _ ≤ ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ *
              ‖((k + 1 + 1 : ℕ) : PadicAlgCl p)‖ := by gcongr
          _ = _ := h1
          _ ≤ ‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * 1 := by gcongr
          _ = _ := mul_one _
      rwa [← div_eq_mul_inv, div_le_iff₀ hkpos] at h3

    have hpow : ((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) < 1 := by
      have h1 : ‖w‖ ^ (k + 1) < ((p : ℝ)⁻¹) ^ (k + 1) :=
        pow_lt_pow_left₀ hw (norm_nonneg _) (Nat.succ_ne_zero k)
      have h2 : ((k + 1 + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (k + 1) := by
        have := Nat.lt_pow_self (n := k + 1) hp.out.one_lt
        exact_mod_cast this
      calc ((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1) < ((k + 1 + 1 : ℕ) : ℝ) * ((p : ℝ)⁻¹) ^ (k + 1) :=
            mul_lt_mul_of_pos_left h1 hkpos
        _ ≤ (p : ℝ) ^ (k + 1) * ((p : ℝ)⁻¹) ^ (k + 1) := by gcongr
        _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
    rw [norm_mul, norm_pow, norm_mul]
    calc ‖w‖ ^ (k + 1 + 1) * ‖((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
        ≤ ‖w‖ ^ (k + 1 + 1) * (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ((k + 1 + 1 : ℕ) : ℝ)) := by
          gcongr
      _ = (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ‖w‖) * (((k + 1 + 1 : ℕ) : ℝ) * ‖w‖ ^ (k + 1)) := by
          ring
      _ < (‖((m' + 1 : ℕ) : PadicAlgCl p)‖ * ‖w‖) * 1 :=
          mul_lt_mul_of_pos_left hpow (mul_pos hmpos hwpos)
      _ = _ := mul_one _
  have htail : ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖
      < ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ := by
    rcases (Finset.range m').eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty, norm_zero]; exact hlead
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty h
        (fun k => w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p))
      exact hle.trans_lt (hterm i hi)
  intro h
  have h0 : (1 + w) ^ (m' + 1) - 1 = 0 := by rw [h, sub_self]
  rw [hexp] at h0
  have hne : ‖((m' + 1 : ℕ) : PadicAlgCl p) * w‖ ≠
      ‖∑ k ∈ Finset.range m', w ^ (k + 1 + 1) * ((m' + 1).choose (k + 1 + 1) : PadicAlgCl p)‖ :=
    htail.ne'
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [h0, norm_zero] at this
  exact hlead.ne (this.trans (max_eq_left htail.le))

end Torsion

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

section Character

theorem cycloChar_toZModPow_eq_one (σ : Gal(PadicAlgCl p/K)) (n : ℕ)
    (h : ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) :
    (cycloChar K σ : ℤ_[p]).toZModPow n = 1 := by
  rw [cycloChar, MonoidHom.comp_apply, cyclotomicCharacter.toZModPow]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact @Subsingleton.elim (ZMod 1) _ _ _
  refine (modularCyclotomicCharacter.unique _ _ _ ?_).symm
  intro t ht
  have hp1 : p ^ n ≠ 1 := (Nat.one_lt_pow hn.ne' hp.out.one_lt).ne'
  rw [ZMod.val_one'' hp1, pow_one]
  have ht' : (t : PadicAlgCl p) ^ p ^ n = 1 := by
    have := (mem_rootsOfUnity _ _).1 ht
    simpa using congrArg Units.val this
  exact h _ ht'

theorem norm_cycloChar_sub_one_le (σ : Gal(PadicAlgCl p/K)) (n : ℕ)
    (h : ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) :
    ‖(cycloChar K σ : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_one, cycloChar_toZModPow_eq_one K σ n h, sub_self]

theorem cycloChar_eq_one_of_forall (σ : Gal(PadicAlgCl p/K))
    (h : ∀ n : ℕ, ∀ ζ : PadicAlgCl p, ζ ^ p ^ n = 1 → σ ζ = ζ) : cycloChar K σ = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycloChar_toZModPow_eq_one K σ n (h n), Units.val_one, map_one]

theorem cycloChar_zpow_ne_one (σ : Gal(PadicAlgCl p/K))
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ) (hne : cycloChar K σ ≠ 1) {j : ℤ}
    (hj : j ≠ 0) : cycloChar K σ ^ j ≠ 1 := by
  intro hpow
  have hm : cycloChar K σ ^ j.natAbs = 1 := by
    rcases Int.natAbs_eq j with hj' | hj'
    · rw [hj', zpow_natCast] at hpow; exact hpow
    · rw [hj', zpow_neg, inv_eq_one, zpow_natCast] at hpow; exact hpow
  set u : ℤ_[p] := ((cycloChar K σ : ℤ_[p]ˣ) : ℤ_[p])
  set w : PadicAlgCl p := algebraMap ℚ_[p] (PadicAlgCl p) ((u - 1 : ℤ_[p]) : ℚ_[p])
  have hw0 : w ≠ 0 := by
    intro hw
    rw [map_eq_zero, PadicInt.coe_eq_zero, sub_eq_zero] at hw
    exact hne (Units.ext hw)
  have hw : ‖w‖ < (p : ℝ)⁻¹ := by
    rw [norm_algebraMap', ← PadicInt.norm_def]
    refine (norm_cycloChar_sub_one_le K σ 2 h2).trans_lt ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    rw [← zpow_neg_one]
    exact zpow_lt_zpow_right₀ hp1 (by norm_num)
  apply one_add_pow_ne_one hw0 hw (Int.natAbs_ne_zero.2 hj)
  have h1 : (1 : PadicAlgCl p) + w = algebraMap ℚ_[p] (PadicAlgCl p) (u : ℚ_[p]) := by
    simp [w, u]
  rw [h1, ← map_pow, ← PadicInt.coe_pow, ← Units.val_pow_eq_pow_val, hm]
  simp

theorem twistScalar_ne_one (σ : Gal(PadicAlgCl p/K))
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ) (hne : cycloChar K σ ≠ 1) {j : ℤ}
    (hj : j ≠ 0) : twistScalar K j σ ≠ 1 := by
  intro h
  rw [twistScalar, ← map_one (algebraMap ℚ_[p] ℂ_[p]),
    (algebraMap ℚ_[p] ℂ_[p]).injective.eq_iff] at h
  have h' : ((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) = 1 := Subtype.ext h
  exact cycloChar_zpow_ne_one K σ h2 hne hj (Units.ext h')

variable [FiniteDimensional ℚ_[p] K]

theorem exists_gal_fix_cyclotomicLayer_cycloChar_ne_one (n : ℕ) :
    ∃ σ : Gal(PadicAlgCl p/K), (∀ y ∈ cyclotomicLayer K n, σ y = y) ∧ cycloChar K σ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  set E : IntermediateField K (PadicAlgCl p) := extendScalars (le_cyclotomicLayer K n)
  have hcyc : ∀ m, cycl p m ≤ cyclotomicLayer K n := by
    intro m
    refine adjoin_le_iff.2 fun ζ hζ => ?_
    have hζ' : ζ ^ p ^ m = 1 := hζ
    have hmem : ζ ∈ fixedField E.fixingSubgroup := by
      rw [mem_fixedField_iff]
      intro σ hσ
      have hσ' : ∀ y ∈ cyclotomicLayer K n, σ y = y := fun y hy =>
        (mem_fixingSubgroup_iff _ _).1 hσ y hy
      have h1 := hcon σ hσ'
      rw [cycloChar_spec K σ hζ', h1, Units.val_one, map_one]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [pow_zero, pow_one] at hζ'
        simp [hζ']
      · have hp1 : p ^ m ≠ 1 := (Nat.one_lt_pow hm.ne' hp.out.one_lt).ne'
        rw [ZMod.val_one'' hp1, pow_one]
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    exact hmem
  have hle := IntermediateField.finrank_le_of_le_right (hcyc (Module.finrank ℚ_[p] (cyclotomicLayer K n) + 1))
  rw [finrank_cycl, Nat.totient_prime_pow_succ hp.out] at hle
  have h1 : Module.finrank ℚ_[p] (cyclotomicLayer K n) < p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) :=
    Nat.lt_pow_self hp.out.one_lt
  have h2 : 1 ≤ p - 1 := by have := hp.out.two_le; omega
  have h3 : p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) ≤
      p ^ Module.finrank ℚ_[p] (cyclotomicLayer K n) * (p - 1) := Nat.le_mul_of_pos_right _ h2
  omega

end Character

section Invariants

noncomputable abbrev cyclotomicLimitGal : Subgroup Gal(PadicAlgCl p/K) :=
  (extendScalars ((le_cyclotomicLayer K 0).trans (cyclotomicLayer_le_cyclotomicLimit K 0))).fixingSubgroup

theorem cycloChar_eq_one_of_mem_cyclotomicLimitGal {σ : Gal(PadicAlgCl p/K)}
    (hσ : σ ∈ cyclotomicLimitGal K) : cycloChar K σ = 1 := by
  refine cycloChar_eq_one_of_forall K σ fun n ζ hζ => ?_
  have hmem : ζ ∈ cyclotomicLimit K :=
    cyclotomicLayer_le_cyclotomicLimit K n (cycl_le_cyclotomicLayer K n (pow_eq_one_mem_cycl hζ))
  exact (mem_fixingSubgroup_iff _ _).1 hσ ζ hmem

theorem mem_cyclotomicCompletion_of_forall_smul_eq {x : ℂ_[p]}
    (hx : ∀ σ ∈ cyclotomicLimitGal K, σ • x = x) : x ∈ cyclotomicCompletion K := by
  have h := fixedPoints_closedSubgroup_eq_closure (cyclotomicLimitGal K)
    (InfiniteGalois.fixingSubgroup_isClosed _)
  have hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ cyclotomicLimitGal K, σ • x = x} := hx
  rw [h, InfiniteGalois.fixedField_fixingSubgroup] at hx'
  exact hx'

variable [FiniteDimensional ℚ_[p] K]

theorem eq_zero_of_forall_twistScalar_mul_smul_eq {j : ℤ} (hj : j ≠ 0) {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), twistScalar K j σ * (σ • x) = x) : x = 0 := by

  have hxc : x ∈ cyclotomicCompletion K := by
    refine mem_cyclotomicCompletion_of_forall_smul_eq K fun σ hσ => ?_
    have h1 : twistScalar K j σ = 1 := by
      simp [twistScalar, cycloChar_eq_one_of_mem_cyclotomicLimitGal K hσ]
    simpa [h1] using hx σ

  have hR : ∀ n, stableIndex K ≤ n → tateTraceHat K n x = 0 := by
    intro n hn
    have key : ∀ σ : Gal(PadicAlgCl p/K),
        tateTraceHat K n x = twistScalar K j σ * (σ • tateTraceHat K n x) := by
      intro σ
      have hc : twistScalar K j σ =
          ((algebraMap ℚ_[p] (PadicAlgCl p) (((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) :
            PadicAlgCl p) : ℂ_[p]) := rfl
      conv_lhs => rw [← hx σ]
      rw [hc, tateTraceHat_mul (IntermediateField.algebraMap_mem _ _) (smul_mem_cyclotomicCompletion σ hxc),
        tateTraceHat_smul n σ hxc]
    obtain ⟨σ, hσ, hne⟩ := exists_gal_fix_cyclotomicLayer_cycloChar_ne_one K n
    have h2 : ∀ ζ : PadicAlgCl p, ζ ^ p ^ 2 = 1 → σ ζ = ζ := fun ζ hζ =>
      hσ ζ (cycl_le_cyclotomicLayer K n (cycl_mono (p := p)
        ((two_le_stableIndex K).trans hn) (pow_eq_one_mem_cycl hζ)))
    obtain ⟨b, hb, hbx⟩ := tateTraceHat_mem n hxc
    have hfix : σ • tateTraceHat K n x = tateTraceHat K n x := by
      rw [← hbx, gal_smul_coe, hσ b hb]
    have h3 := key σ
    rw [hfix] at h3
    have h4 : (twistScalar K j σ - 1) * tateTraceHat K n x = 0 := by
      rw [sub_mul, one_mul, ← h3, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (twistScalar_ne_one K σ h2 hne hj))

  set c := tateBound K
  have hc0 : 0 ≤ c := tateBound_nonneg K
  have hbound : ∀ ε > 0, ‖x‖ ≤ (1 + c) * ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hxc ε hε
    obtain ⟨m, hm⟩ := (mem_cyclotomicLimit K).1 hy
    set m' := max m (stableIndex K)
    have hym : y ∈ cyclotomicLayer K m' := cyclotomicLayer_mono K (le_max_left _ _) hm
    have hyc : (y : ℂ_[p]) ∈ cyclotomicCompletion K := coe_mem_closureInCp hy
    have hsub : (y : ℂ_[p]) - x ∈ cyclotomicCompletion K := sub_mem_closureInCp hyc hxc
    have h1 : tateTraceHat K m' (y : ℂ_[p]) =
        tateTraceHat K m' ((y : ℂ_[p]) - x) + tateTraceHat K m' x := by
      rw [← tateTraceHat_add m' hsub hxc, sub_add_cancel]
    rw [tateTraceHat_coe_of_mem hym, hR m' (le_max_right _ _), add_zero] at h1
    have h2 : ‖(y : ℂ_[p])‖ ≤ c * ε := by
      rw [h1]
      refine (norm_tateTraceHat_le m' hsub).trans ?_
      rw [← dist_eq_norm, dist_comm]
      exact mul_le_mul_of_nonneg_left hxy.le hc0
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - (y : ℂ_[p])‖ + ‖(y : ℂ_[p])‖ := norm_add_le _ _
      _ ≤ ε + c * ε := add_le_add (by rw [← dist_eq_norm]; exact hxy.le) h2
      _ = (1 + c) * ε := by ring
  by_contra hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h := hbound (‖x‖ / (2 * (1 + c))) (by positivity)
  have h' : (1 + c) * (‖x‖ / (2 * (1 + c))) = ‖x‖ / 2 := by
    field_simp
  rw [h'] at h
  linarith

theorem cpTwistRep_invariants_zero :
    (cpTwistRep K 0).invariants = LinearMap.range (Algebra.linearMap K ℂ_[p]) := by
  ext x
  rw [ContRepresentation.mem_invariants, LinearMap.mem_range]
  simp only [cpTwistRep_apply, twistScalar_zero, one_mul, Algebra.linearMap_apply]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_eq_coe_of_forall_smul_eq (K := K) h
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩ σ
    exact gal_smul_algebraMap_intermediateField K σ k

theorem cpTwistRep_invariants_eq_bot {j : ℤ} (hj : j ≠ 0) : (cpTwistRep K j).invariants = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [ContRepresentation.mem_invariants] at hx
  exact (Submodule.mem_bot K).2 (eq_zero_of_forall_twistScalar_mul_smul_eq K hj hx)

end Invariants

end GroundTheory.PAdicHodge
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open TensorProduct Module

section Field

variable (G F B : Type*) [Group G] [Field F] [Field B] [Algebra F B] [MulSemiringAction G B]

theorem isRegular_of_field : IsRegular G F B where
  image_fixedPoints := by
    let := IsFractionRing.mulSemiringAction G B (FractionRing B)
    have hmap : ∀ (g : G) (b : B), g • algebraMap B (FractionRing B) b =
        algebraMap B (FractionRing B) (g • b) := fun g b =>
      IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
    have hinj := IsFractionRing.injective B (FractionRing B)
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩ g
      rw [hmap, hb g]
    · intro hy
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors B) y
      have hs : (s : B) ≠ 0 := nonZeroDivisors.ne_zero s.2
      have e : IsLocalization.mk' (FractionRing B) a s =
          algebraMap B (FractionRing B) (a * (s : B)⁻¹) := by
        rw [IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, mul_assoc, inv_mul_cancel₀ hs, mul_one]
      refine ⟨a * (s : B)⁻¹, fun g => hinj ?_, e.symm⟩
      rw [← hmap, ← e]
      exact hy g
  isUnit_of_mem_span b hb _ := hb.isUnit

end Field

section Coeff

variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)

def DBK : Submodule K (B ⊗[F] V) where
  carrier := {x | ∀ g : G, baseChangeRep B ρ g x = x}
  add_mem' {x y} hx hy g := by rw [map_add, hx g, hy g]
  zero_mem' g := map_zero _
  smul_mem' k x hx g := by
    change baseChangeRep B ρ g (k • x) = k • x
    rw [← algebraMap_smul B k x, baseChangeRep_smul, hx g, smul_algebraMap]

variable {G F K B ρ} in
theorem mem_DBK {x : B ⊗[F] V} : x ∈ DBK G F K B ρ ↔ ∀ g : G, baseChangeRep B ρ g x = x :=
  Iff.rfl


def toInvariantRing : K →+* invariantRing G F B where
  toFun k := ⟨algebraMap K B k, fun g => smul_algebraMap g k⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

variable {G F K B}

omit [Algebra F K] [IsScalarTower F K B] in
@[simp]
theorem coe_toInvariantRing (k : K) : (toInvariantRing G F K B k : B) = algebraMap K B k := rfl

omit [Algebra F K] [IsScalarTower F K B] in
theorem toInvariantRing_bijective [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    Function.Bijective (toInvariantRing G F K B) := by
  refine ⟨fun a b hab => (algebraMap K B).injective ?_, fun e => ?_⟩
  · simpa using congrArg Subtype.val hab
  · obtain ⟨k, hk⟩ := hK e e.2
    exact ⟨k, Subtype.ext hk⟩


theorem rank_DBK [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    Module.rank K (DBK G F K B ρ) = Module.rank (invariantRing G F B) (DB B ρ) := by
  let j : DBK G F K B ρ ≃+ DB B ρ :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  refine rank_eq_of_equiv_equiv (toInvariantRing G F K B) j (toInvariantRing_bijective hK) ?_
  intro k x
  apply Subtype.ext
  change k • (x : B ⊗[F] V) =
    ((toInvariantRing G F K B k : invariantRing G F B) : B) • (x : B ⊗[F] V)
  rw [coe_toInvariantRing, algebraMap_smul]

theorem finrank_DBK [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    finrank K (DBK G F K B ρ) = finrank (invariantRing G F B) (DB B ρ) := by
  simp only [Module.finrank, rank_DBK ρ hK]

variable [IsDomain B]

theorem IsRegular.finiteDimensional_DBK (h : IsRegular G F B)
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) [FiniteDimensional F V] :
    FiniteDimensional K (DBK G F K B ρ) := by
  let := h.field
  have := h.free ρ
  have := h.finite ρ
  have : Module.Free K (DBK G F K B ρ) := Module.Free.of_divisionRing K (DBK G F K B ρ)
  exact Module.rank_lt_aleph0_iff.1 (by rw [rank_DBK ρ hK]; exact Module.rank_lt_aleph0_iff.2 ‹_›)


theorem isAdmissible_iff_finrank_DBK
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    IsAdmissible B ρ ↔ finrank K (DBK G F K B ρ) = finrank F V := by
  rw [finrank_DBK ρ hK]
  rfl

end Coeff

end GroundTheory.PAdicHodge
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open IsLocalRing TensorProduct Module

namespace GroundTheory.PAdicHodge

variable {p : ℕ} [Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p
local notation "Fil" => IsPerfectoidField.fil ℂ_[p] p

section Algebra

variable (p) in

def algClToBdRField : PadicAlgCl p →+* 𝔹dR := (algebraMap 𝔹 𝔹dR).comp (algClToBdR p).toRingHom

instance algebraAlgClBDeRham : Algebra (PadicAlgCl p) 𝔹dR := (algClToBdRField p).toAlgebra

instance algebraPadicBDeRham : Algebra ℚ_[p] 𝔹dR :=
  ((algebraMap 𝔹 𝔹dR).comp (algebraMap ℚ_[p] 𝔹)).toAlgebra

theorem algebraMap_padic_bDeRham (q : ℚ_[p]) :
    algebraMap ℚ_[p] 𝔹dR q = algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) := rfl


instance isScalarTower_padic_bDeRhamPlus_bDeRham : IsScalarTower ℚ_[p] 𝔹 𝔹dR :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance isScalarTower_padic_algCl_bDeRham : IsScalarTower ℚ_[p] (PadicAlgCl p) 𝔹dR :=
  IsScalarTower.of_algebraMap_eq fun q => by
    change algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) =
      algebraMap 𝔹 𝔹dR (algClToBdR p (algebraMap ℚ_[p] (PadicAlgCl p) q))
    rw [AlgHom.commutes]

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem algebraMap_intermediateField_bDeRham (k : K) :
    algebraMap K 𝔹dR k = algebraMap 𝔹 𝔹dR (algClToBdR p k) := rfl

instance isScalarTower_padic_intermediateField_bDeRham : IsScalarTower ℚ_[p] K 𝔹dR :=
  IsScalarTower.of_algebraMap_eq fun q => by
    change algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) =
      algebraMap 𝔹 𝔹dR (algClToBdR p (algebraMap ℚ_[p] (PadicAlgCl p) q))
    rw [AlgHom.commutes]

variable {K}

theorem gal_smul_algebraMap_intermediateField_bDeRham (σ : Gal(PadicAlgCl p/K)) (k : K) :
    σ • algebraMap K 𝔹dR k = algebraMap K 𝔹dR k := by
  rw [algebraMap_intermediateField_bDeRham, gal_smul_algebraMap_bDeRham, gal_smul_algClToBdR]
  congr 2
  exact AlgEquiv.commutes σ k

theorem gal_smul_algebraMap_padic_bDeRham (σ : Gal(PadicAlgCl p/K)) (q : ℚ_[p]) :
    σ • algebraMap ℚ_[p] 𝔹dR q = algebraMap ℚ_[p] 𝔹dR q := by
  rw [algebraMap_padic_bDeRham, gal_smul_algebraMap_bDeRham, gal_smul_algebraMap_bdR]

instance smulCommClass_gal_intermediateField_bDeRham :
    SMulCommClass Gal(PadicAlgCl p/K) K 𝔹dR where
  smul_comm σ k x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', gal_smul_algebraMap_intermediateField_bDeRham]

instance smulCommClass_gal_padic_bDeRham : SMulCommClass Gal(PadicAlgCl p/K) ℚ_[p] 𝔹dR where
  smul_comm σ q x := by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', gal_smul_algebraMap_padic_bDeRham]

end Algebra

section Level

theorem bDeRham_exists_mem_fil (x : 𝔹dR) : ∃ i : ℤ, x ∈ Fil i := by
  have hx : x ∈ ⨆ i, Fil i := by
    rw [IsPerfectoidField.iSup_fil]
    exact Submodule.mem_top
  exact (Submodule.mem_iSup_of_directed _
    (IsPerfectoidField.fil_antitone ℂ_[p] p).directed_le).1 hx

theorem bDeRham_exists_not_mem_fil {x : 𝔹dR} (hx : x ≠ 0) : ∃ i : ℤ, x ∉ Fil i := by
  by_contra h
  push Not at h
  apply hx
  have : x ∈ ⨅ i, Fil i := (Submodule.mem_iInf _).2 h
  rwa [IsPerfectoidField.iInf_fil, Submodule.mem_bot] at this

theorem bDeRham_exists_level {x : 𝔹dR} (hx : x ≠ 0) : ∃ i : ℤ, x ∈ Fil i ∧ x ∉ Fil (i + 1) := by
  obtain ⟨j, hj⟩ := bDeRham_exists_not_mem_fil hx
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, x ∈ Fil z → z ≤ b := by
    refine ⟨j, fun z hz => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hj (IsPerfectoidField.fil_antitone ℂ_[p] p hlt.le hz)
  obtain ⟨i, hi, hmax⟩ := Int.exists_greatest_of_bdd hbdd (bDeRham_exists_mem_fil x)
  exact ⟨i, hi, fun h => by have := hmax _ h; omega⟩

theorem bDeRham_exists_forall_mem_fil {ι : Type*} (s : Finset ι) (c : ι → 𝔹dR) :
    ∃ i : ℤ, ∀ j ∈ s, c j ∈ Fil i := by
  classical
  refine Finset.induction_on s ⟨0, by simp⟩ ?_
  rintro a s - ⟨i, hi⟩
  obtain ⟨i', hi'⟩ := bDeRham_exists_mem_fil (c a)
  refine ⟨min i i', fun j hj => ?_⟩
  rcases Finset.mem_insert.1 hj with rfl | hj
  · exact IsPerfectoidField.fil_antitone ℂ_[p] p (min_le_right _ _) hi'
  · exact IsPerfectoidField.fil_antitone ℂ_[p] p (min_le_left _ _) (hi j hj)

theorem grMap_zero_algebraMap (b : 𝔹) (h : algebraMap 𝔹 𝔹dR b ∈ Fil 0) :
    IsPerfectoidField.grMap maximalIdeal_eq_span_tBdR 0 ⟨algebraMap 𝔹 𝔹dR b, h⟩ =
      thetaAlgHom p b := by
  have e : algebraMap 𝔹 𝔹dR b = algebraMap 𝔹 𝔹dR (tBdR p) ^ (0 : ℤ) * algebraMap 𝔹 𝔹dR b := by
    rw [zpow_zero, one_mul]
  have h' : algebraMap 𝔹 𝔹dR (tBdR p) ^ (0 : ℤ) * algebraMap 𝔹 𝔹dR b ∈ Fil 0 := by
    rw [← e]
    exact h
  have : (⟨algebraMap 𝔹 𝔹dR b, h⟩ : Fil 0) = ⟨_, h'⟩ := Subtype.ext e
  rw [this, IsPerfectoidField.grMap_mk, thetaAlgHom_apply]

end Level

section Invariants

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem grMap_mem_invariants {i : ℤ} (x : Fil i)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • (x : 𝔹dR) = x) :
    IsPerfectoidField.grMap maximalIdeal_eq_span_tBdR i x ∈ (cpTwistRep K i).invariants := by
  rw [ContRepresentation.mem_invariants]
  intro σ
  rw [← grMap_tBdR_gal_smul σ x]
  congr 1
  exact Subtype.ext (hx σ)

variable [FiniteDimensional ℚ_[p] K]

theorem mem_fil_succ_of_invariant {i : ℤ} (hi : i ≠ 0) {x : 𝔹dR} (hxi : x ∈ Fil i)
    (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) : x ∈ Fil (i + 1) := by
  have h := grMap_mem_invariants K ⟨x, hxi⟩ hx
  rw [cpTwistRep_invariants_eq_bot K hi, Submodule.mem_bot] at h
  exact (IsPerfectoidField.grMap_eq_zero_iff maximalIdeal_eq_span_tBdR ⟨x, hxi⟩).1 h

theorem level_eq_zero_of_invariant {x : 𝔹dR} (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x)
    {i : ℤ} (hi : x ∈ Fil i) (hi' : x ∉ Fil (i + 1)) : i = 0 := by
  by_contra h
  exact hi' (mem_fil_succ_of_invariant K h hi hx)

theorem bDeRham_fixed (x : 𝔹dR) (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) :
    ∃ k : K, algebraMap K 𝔹dR k = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by rw [map_zero, h0]⟩
  obtain ⟨i, hi, hi'⟩ := bDeRham_exists_level h0
  obtain rfl := level_eq_zero_of_invariant K hx hi hi'
  have hinv := grMap_mem_invariants K ⟨x, hi⟩ hx
  rw [cpTwistRep_invariants_zero K] at hinv
  obtain ⟨k, hk⟩ := hinv
  refine ⟨k, ?_⟩
  rw [algebraMap_intermediateField_bDeRham]
  by_contra hne
  have hy0 : x - algebraMap 𝔹 𝔹dR (algClToBdR p k) ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hyinv : ∀ σ : Gal(PadicAlgCl p/K), σ • (x - algebraMap 𝔹 𝔹dR (algClToBdR p k)) =
      x - algebraMap 𝔹 𝔹dR (algClToBdR p k) := fun σ => by
    rw [smul_sub, hx σ, ← algebraMap_intermediateField_bDeRham,
      gal_smul_algebraMap_intermediateField_bDeRham]
  have hk0 : algebraMap 𝔹 𝔹dR (algClToBdR p k) ∈ Fil 0 :=
    (IsPerfectoidField.mem_fil_zero_iff ℂ_[p] p).2 ⟨_, rfl⟩
  have hgr0 := grMap_zero_algebraMap (algClToBdR p k) hk0
  rw [thetaAlgHom_algClToBdR] at hgr0
  have hy : x - algebraMap 𝔹 𝔹dR (algClToBdR p k) ∈ Fil 0 := Submodule.sub_mem _ hi hk0
  have hgr : IsPerfectoidField.grMap maximalIdeal_eq_span_tBdR 0
      (⟨x - algebraMap 𝔹 𝔹dR (algClToBdR p k), hy⟩ : Fil 0) = 0 := by
    have e : (⟨x - algebraMap 𝔹 𝔹dR (algClToBdR p k), hy⟩ : Fil 0) =
        ⟨x, hi⟩ - ⟨algebraMap 𝔹 𝔹dR (algClToBdR p k), hk0⟩ := rfl
    rw [e, map_sub, hgr0, ← hk, Algebra.linearMap_apply, algebraMap_intermediateField_cp, sub_self]
  have hy1 : x - algebraMap 𝔹 𝔹dR (algClToBdR p k) ∈ Fil (0 + 1) :=
    (IsPerfectoidField.grMap_eq_zero_iff maximalIdeal_eq_span_tBdR _).1 hgr
  obtain ⟨j, hj, hj'⟩ := bDeRham_exists_level hy0
  obtain rfl := level_eq_zero_of_invariant K hyinv hj hj'
  exact hj' hy1

theorem bDeRhamPlus_fixed (b : 𝔹) (hb : ∀ σ : Gal(PadicAlgCl p/K), σ • b = b) :
    ∃ k : K, algClToBdR p k = b := by
  obtain ⟨k, hk⟩ := bDeRham_fixed K (algebraMap 𝔹 𝔹dR b) fun σ => by
    rw [gal_smul_algebraMap_bDeRham, hb σ]
  exact ⟨k, IsPerfectoidField.algebraMap_bDeRham_injective hk⟩


end Invariants

section DeRham

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isRegular_bDeRham : IsRegular Gal(PadicAlgCl p/K) ℚ_[p] 𝔹dR :=
  isRegular_of_field _ _ _

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V)

abbrev DdR : Submodule K (𝔹dR ⊗[ℚ_[p]] V) := DBK Gal(PadicAlgCl p/K) ℚ_[p] K 𝔹dR ρ

def IsDeRham : Prop := IsAdmissible 𝔹dR ρ

variable [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] V]

theorem finiteDimensional_DdR : FiniteDimensional K (DdR K ρ) :=
  (isRegular_bDeRham K).finiteDimensional_DBK ρ (bDeRham_fixed K)


omit [FiniteDimensional ℚ_[p] V] in

theorem isDeRham_iff_finrank : IsDeRham K ρ ↔ finrank K (DdR K ρ) = finrank ℚ_[p] V :=
  isAdmissible_iff_finrank_DBK ρ (bDeRham_fixed K)

omit [FiniteDimensional ℚ_[p] K] in

theorem IsDeRham.comparison_bijective (h : IsDeRham K ρ) :
    Function.Bijective (comparison 𝔹dR ρ) :=
  ((isRegular_bDeRham K).isAdmissible_iff_bijective ρ).1 h

end DeRham

section Filtration

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (V : Type*) [AddCommGroup V]
  [Module ℚ_[p] V]

def filTensor (i : ℤ) : Submodule K (𝔹dR ⊗[ℚ_[p]] V) :=
  Submodule.span K {x | ∃ b ∈ Fil i, ∃ v : V, x = b ⊗ₜ v}

variable {K V}

theorem mem_filTensor_iff {ι : Type*} [Fintype ι] (v : Basis ι ℚ_[p] V) {i : ℤ}
    {x : 𝔹dR ⊗[ℚ_[p]] V} :
    x ∈ filTensor K V i ↔ ∀ j, (Algebra.TensorProduct.basis 𝔹dR v).repr x j ∈ Fil i := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, w, rfl⟩ := hx
      intro j
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, mul_comm, algebraMap_padic_bDeRham, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hb
    | zero => simp
    | add x y _ _ hx hy =>
      intro j
      rw [map_add, Finsupp.add_apply]
      exact add_mem (hx j) (hy j)
    | smul k x _ hx =>
      intro j
      rw [← algebraMap_smul 𝔹dR k x, map_smul, Finsupp.smul_apply, smul_eq_mul,
        algebraMap_intermediateField_bDeRham, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hx j)
  · intro h
    rw [← (Algebra.TensorProduct.basis 𝔹dR v).sum_repr x]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨_, h j, v j, ?_⟩
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable (K V) in

theorem filTensor_antitone : Antitone (filTensor K V) := fun _ _ hij =>
  Submodule.span_mono fun _ ⟨b, hb, w, hx⟩ =>
    ⟨b, IsPerfectoidField.fil_antitone ℂ_[p] p hij hb, w, hx⟩

variable [FiniteDimensional ℚ_[p] V]

theorem exists_mem_filTensor (x : 𝔹dR ⊗[ℚ_[p]] V) : ∃ i : ℤ, x ∈ filTensor K V i := by
  let v := Module.finBasis ℚ_[p] V
  obtain ⟨i, hi⟩ := bDeRham_exists_forall_mem_fil Finset.univ
    ((Algebra.TensorProduct.basis 𝔹dR v).repr x)
  exact ⟨i, (mem_filTensor_iff v).2 fun j => hi j (Finset.mem_univ j)⟩

theorem exists_not_mem_filTensor {x : 𝔹dR ⊗[ℚ_[p]] V} (hx : x ≠ 0) :
    ∃ i : ℤ, x ∉ filTensor K V i := by
  let v := Module.finBasis ℚ_[p] V
  have : (Algebra.TensorProduct.basis 𝔹dR v).repr x ≠ 0 := by
    rwa [Ne, LinearEquiv.map_eq_zero_iff]
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 this
  obtain ⟨i, hi⟩ := bDeRham_exists_not_mem_fil hj
  exact ⟨i, fun h => hi ((mem_filTensor_iff v).1 h j)⟩

theorem exists_forall_mem_filTensor {ι : Type*} (s : Finset ι) (x : ι → 𝔹dR ⊗[ℚ_[p]] V) :
    ∃ i : ℤ, ∀ j ∈ s, x j ∈ filTensor K V i := by
  classical
  refine Finset.induction_on s ⟨0, by simp⟩ ?_
  rintro a s - ⟨i, hi⟩
  obtain ⟨i', hi'⟩ := exists_mem_filTensor (K := K) (x a)
  refine ⟨min i i', fun j hj => ?_⟩
  rcases Finset.mem_insert.1 hj with rfl | hj
  · exact filTensor_antitone K V (min_le_right _ _) hi'
  · exact filTensor_antitone K V (min_le_left _ _) (hi j hj)

variable (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V)

variable (K) in

def filDdR (i : ℤ) : Submodule K (𝔹dR ⊗[ℚ_[p]] V) := DdR K ρ ⊓ filTensor K V i

omit [FiniteDimensional ℚ_[p] V] in
variable (K) in

theorem filDdR_antitone : Antitone (filDdR K ρ) := fun _ _ hij =>
  inf_le_inf_left _ (filTensor_antitone K V hij)

omit [FiniteDimensional ℚ_[p] V] in
theorem filDdR_le (i : ℤ) : filDdR K ρ i ≤ DdR K ρ := inf_le_left

variable [FiniteDimensional ℚ_[p] K]

variable (K) in

theorem exists_filDdR_eq_top : ∃ a : ℤ, filDdR K ρ a = DdR K ρ := by
  have := finiteDimensional_DdR K ρ
  have : Module.Free K (DdR K ρ) := Module.Free.of_divisionRing K (DdR K ρ)
  let d := Module.finBasis K (DdR K ρ)
  obtain ⟨a, ha⟩ := exists_forall_mem_filTensor (K := K) Finset.univ fun l => (d l : 𝔹dR ⊗[ℚ_[p]] V)
  refine ⟨a, le_antisymm inf_le_left fun x hx => ⟨hx, ?_⟩⟩
  have hsum := congrArg Subtype.val (d.sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
  rw [← hsum]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (ha l (Finset.mem_univ l))

variable (K) in

theorem exists_filDdR_eq_bot : ∃ b : ℤ, filDdR K ρ b = ⊥ := by
  have := finiteDimensional_DdR K ρ
  have key : ∀ n : ℕ, ∀ i : ℤ, finrank K (filDdR K ρ i) ≤ n → ∃ b : ℤ, filDdR K ρ b = ⊥ := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have : FiniteDimensional K (filDdR K ρ i) :=
        Submodule.finiteDimensional_of_le (filDdR_le ρ i)
      exact ⟨i, Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hi)⟩
    | succ n ih =>
      intro i hi
      by_cases hbot : filDdR K ρ i = ⊥
      · exact ⟨i, hbot⟩
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨j, hj⟩ := exists_not_mem_filTensor (K := K) hx0
      have hij : i ≤ j := by
        by_contra hlt
        push Not at hlt
        exact hj (filTensor_antitone K V hlt.le hx.2)
      have hlt : filDdR K ρ j < filDdR K ρ i :=
        lt_of_le_of_ne (filDdR_antitone K ρ hij) fun heq => hj (heq ▸ hx).2
      have : FiniteDimensional K (filDdR K ρ i) :=
        Submodule.finiteDimensional_of_le (filDdR_le ρ i)
      exact ih j (Nat.lt_succ_iff.1 ((Submodule.finrank_lt_finrank_of_lt hlt).trans_le hi))
  exact key _ 0 le_rfl

end Filtration

end GroundTheory.PAdicHodge
end
end
