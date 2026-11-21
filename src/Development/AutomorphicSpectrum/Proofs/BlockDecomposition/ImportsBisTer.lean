import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantIwahoriCosetReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorCosetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnLeviCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFixedVectorProjection
import BuildAid.ForwardExisting
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPowTendstoZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsFixedLift
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VecStab

section
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem jacquet_hecke_operator_compat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C2 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hI hpos V _ _ π hπ t ht T hT v
  obtain ⟨r, hr, x, hx, hu⟩ := GlobalTheory.T.dominant_iwahori_coset_reps k N h d hd J hJo hJc hI hpos t ht
  have key := GlobalTheory.T.hecke_operator_coset_sum k N J hJc V π hπ (leviEmb k (stdBlocks d hd) t) T hT r x hr
    (fun i => (hx i).1) hu v
  have hmk : ∀ i, (Submodule.Quotient.mk (π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) t) (v : V)) := by
    intro i
    rw [Submodule.Quotient.eq]
    refine Submodule.subset_span ⟨⟨x i, (hx i).2⟩, π (leviEmb k (stdBlocks d hd) t) (v : V), ?_⟩
    simp [map_mul]
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
  have hsum : (Submodule.Quotient.mk ((T v : fixed π J) : V) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) t) (v : V)) := by
    rw [key, Submodule.Quotient.mk_smul]
    have h2 : (Submodule.Quotient.mk (∑ i, π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :
        Jacquet π (unipRad k (stdBlocks d hd))) =
        ∑ i : Fin r, Submodule.Quotient.mk (π (x i * leviEmb k (stdBlocks d hd) t) (v : V)) :=
      map_sum (Submodule.mkQ _) _ _
    rw [h2, Finset.sum_congr rfl fun i _ => hmk i]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  rw [hsum, jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end GlobalTheory.CompanionTheory.Lbc
end

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_hecke_compat_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C2 k := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Lbc.jacquet_hecke_operator_compat
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.HeckeExist

theorem exists_heckeOp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.CH k := by
  intro k _ _ _ _ N J _ hJc V _ _ π hπ g
  obtain ⟨E, hE1, -, hE3, -, -⟩ :=
    GlobalTheory.CompanionTheory.CompactAvg.exists_average (GL (Fin N) k) J hJc V π hπ
  refine ⟨((E ∘ₗ π g ∘ₗ (fixed π J).subtype).codRestrict (fixed π J) (fun v => hE1 _)), ?_⟩
  intro v l hl
  have h := LinearMap.congr_fun (hE3 l hl) (π g (v : V))
  simpa using h.symm

end GlobalTheory.CompanionTheory.HeckeExist
end

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_hecke_condition_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.CH k := by
  atlas_forward_decl GlobalTheory.CompanionTheory.HeckeExist.exists_heckeOp
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.CentralDom

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {N : ℕ}

theorem coe_diagPow (l : Fin N → ℤ) :
    ((Zls.diagPow k N l : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ l i : kˣ) : k) := by
  ext i j
  simp [Zls.diagPow, Matrix.diagonal_apply]

theorem diagPow_add (l l' : Fin N → ℤ) :
    Zls.diagPow k N (l + l') = Zls.diagPow k N l * Zls.diagPow k N l' := by
  apply Units.ext
  rw [Units.val_mul, coe_diagPow, coe_diagPow, coe_diagPow, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, _root_.zpow_add, Units.val_mul]

theorem diagPow_zero : Zls.diagPow k N 0 = 1 := by
  apply Units.ext
  rw [coe_diagPow]
  simp

theorem diagPow_neg (l : Fin N → ℤ) : Zls.diagPow k N (-l) = (Zls.diagPow k N l)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← diagPow_add, neg_add_cancel, diagPow_zero]

theorem diagPow_pow (l : Fin N → ℤ) (j : ℕ) :
    Zls.diagPow k N l ^ j = Zls.diagPow k N ((j : ℤ) • l) := by
  induction j with
  | zero => simp [diagPow_zero]
  | succ j ih =>
    rw [pow_succ, ih, ← diagPow_add]
    congr 1
    funext i
    simp
    ring

theorem conj_apply (l : Fin N → ℤ) (y : GL (Fin N) k) (i j : Fin N) :
    ((Zls.diagPow k N l * y * (Zls.diagPow k N l)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      ((Zls.unifU k ^ (l i - l j) : kˣ) : k) * (y : Matrix (Fin N) (Fin N) k) i j := by
  rw [← diagPow_neg, Units.val_mul, Units.val_mul, coe_diagPow, coe_diagPow, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.neg_apply, sub_eq_add_neg, _root_.zpow_add, Units.val_mul]
  ring

def contractMat (l : Fin N → ℤ) (s : k) (m : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k :=
  Matrix.of fun i j => if l j < l i then s ^ (l i - l j).toNat * m i j else (1 : Matrix (Fin N) (Fin N) k) i j

theorem continuous_contractMat (l : Fin N → ℤ) {X : Type} [TopologicalSpace X] {f : X → k}
    {g : X → Matrix (Fin N) (Fin N) k} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => contractMat l (f x) (g x) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : l j < l i
  · simp only [contractMat, Matrix.of_apply, h, if_true]
    exact (hf.pow _).mul (hg.matrix_elem i j)
  · simp only [contractMat, Matrix.of_apply, h, if_false]
    exact continuous_const

theorem contractMat_zero (l : Fin N → ℤ) (m : Matrix (Fin N) (Fin N) k) : contractMat l 0 m = 1 := by
  ext i j
  by_cases h : l j < l i
  · have hij : i ≠ j := fun e => by subst e; exact lt_irrefl _ h
    have he : (l i - l j).toNat ≠ 0 := by omega
    simp [contractMat, h, hij, he]
  · simp [contractMat, h]

theorem val_conj_eq (l : Fin N → ℤ) (c : ℕ) (y : GL (Fin N) k)
    (hy : ∀ i j, l i ≤ l j → (y : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j) :
    ((Zls.diagPow k N ((c : ℤ) • l) * y * (Zls.diagPow k N ((c : ℤ) • l))⁻¹ : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) =
      contractMat l (((Zls.unifU k : kˣ) : k) ^ c) (y : Matrix (Fin N) (Fin N) k) := by
  ext i j
  rw [conj_apply]
  by_cases h : l j < l i
  · simp only [contractMat, Matrix.of_apply, h, if_true]
    congr 1
    have he : ((l i - l j).toNat : ℤ) = l i - l j := Int.toNat_of_nonneg (by omega)
    have : ((c : ℤ) • l) i - ((c : ℤ) • l) j = ((c * (l i - l j).toNat : ℕ) : ℤ) := by
      push_cast
      rw [he]
      simp
      ring
    rw [this, zpow_natCast, Units.val_pow_eq_pow_val, pow_mul]
  · have h' : l i ≤ l j := not_lt.1 h
    simp only [contractMat, Matrix.of_apply, h, if_false]
    rw [hy i j h']
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]

theorem exists_contract (l : Fin N → ℤ) (J : Subgroup (GL (Fin N) k))
    (hJ : IsCompact (J : Set (GL (Fin N) k))) (S : Subgroup (GL (Fin N) k))
    (hS : ∀ y ∈ S, ∀ i j, l i ≤ l j →
      (y : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j)
    (U : Set (GL (Fin N) k)) (hU : IsOpen U) (h1 : (1 : GL (Fin N) k) ∈ U) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∀ y ∈ J, y ∈ S →
      Zls.diagPow k N ((c : ℤ) • l) * y * (Zls.diagPow k N ((c : ℤ) • l))⁻¹ ∈ U := by
  obtain ⟨W, hWo, rfl⟩ := isOpen_induced_iff.1 hU
  let Φ : k × GL (Fin N) k → Matrix (Fin N) (Fin N) k × (Matrix (Fin N) (Fin N) k)ᵐᵒᵖ := fun p =>
    (contractMat l p.1 (p.2 : Matrix (Fin N) (Fin N) k),
      MulOpposite.op (contractMat l p.1 ((p.2⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)))
  have hΦ : Continuous Φ := by
    refine Continuous.prodMk ?_ (MulOpposite.continuous_op.comp ?_)
    · exact continuous_contractMat l continuous_fst (Units.continuous_val.comp continuous_snd)
    · exact continuous_contractMat l continuous_fst
        (Units.continuous_val.comp (continuous_inv.comp continuous_snd))
  have hsub : ({0} : Set k) ×ˢ (J : Set (GL (Fin N) k)) ⊆ Φ ⁻¹' W := by
    rintro ⟨s, y⟩ ⟨hs, -⟩
    obtain rfl : s = 0 := hs
    have : Φ (0, y) = Units.embedProduct _ (1 : GL (Fin N) k) := by
      rw [map_one]
      show (contractMat l 0 _, MulOpposite.op (contractMat l 0 _)) = 1
      rw [contractMat_zero, contractMat_zero]
      rfl
    show Φ (0, y) ∈ W
    rw [this]
    exact h1
  obtain ⟨u, v, hu, -, h0u, hJv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hJ (hWo.preimage hΦ) hsub
  have hev := (GlobalTheory.CompanionTheory.UnifPow.tendsto_unifU_pow k).eventually (hu.mem_nhds (h0u rfl))
  obtain ⟨c₀, hc₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨c₀, fun c hc y hyJ hyS => ?_⟩
  have hin : Φ (((Zls.unifU k : kˣ) : k) ^ c, y) ∈ W := huv ⟨hc₀ c hc, hJv hyJ⟩
  have hinv : (Zls.diagPow k N ((c : ℤ) • l) * y * (Zls.diagPow k N ((c : ℤ) • l))⁻¹)⁻¹ =
      Zls.diagPow k N ((c : ℤ) • l) * y⁻¹ * (Zls.diagPow k N ((c : ℤ) • l))⁻¹ := by
    group
  show Units.embedProduct _ _ ∈ W
  have : Units.embedProduct _ (Zls.diagPow k N ((c : ℤ) • l) * y * (Zls.diagPow k N ((c : ℤ) • l))⁻¹) =
      Φ (((Zls.unifU k : kˣ) : k) ^ c, y) := by
    simp only [Units.embedProduct_apply, Φ]
    rw [hinv, val_conj_eq l c y (hS y hyS), val_conj_eq l c y⁻¹ (hS _ (inv_mem hyS))]
  rw [this]
  exact hin

variable {h : ℕ}

def zLevi (d : Fin h → ℕ) (w : Fin h → ℤ) : Levi k (Bl d) :=
  fun b => Matrix.GeneralLinearGroup.scalar (Fin (d b)) (Zls.unifU k ^ w b)

theorem coe_zLevi (d : Fin h → ℕ) (w : Fin h → ℤ) (b : Fin h) :
    ((zLevi d w b : GL (Fin (d b)) k) : Matrix (Fin (d b)) (Fin (d b)) k) =
      Matrix.scalar (Fin (d b)) ((Zls.unifU k ^ w b : kˣ) : k) := rfl

theorem zLevi_comm (d : Fin h → ℕ) (w : Fin h → ℤ) (x : Levi k (Bl d)) :
    zLevi d w * x = x * zLevi d w := by
  funext b
  apply Units.ext
  show ((zLevi d w b : GL (Fin (d b)) k) : Matrix (Fin (d b)) (Fin (d b)) k) * (x b : GL (Fin (d b)) k) =
    ((x b : GL (Fin (d b)) k) : Matrix (Fin (d b)) (Fin (d b)) k) * (zLevi d w b : GL (Fin (d b)) k)
  rw [coe_zLevi]
  exact Matrix.scalar_commute _ (fun r => Commute.all _ r) _

theorem stdBlocks_ne (d : Fin h → ℕ) (hd : ∑ a, d a = N) {a b : Fin h} (i : Fin (d a)) (j : Fin (d b))
    (hab : (⟨a, i⟩ : Σ a, Fin (d a)) ≠ ⟨b, j⟩) : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨b, j⟩ :=
  fun e => hab ((stdBlocks d hd).injective e)

theorem leviEmb_zLevi (d : Fin h → ℕ) (hd : ∑ a, d a = N) (w : Fin h → ℤ) :
    leviEmb k (stdBlocks d hd) (zLevi d w) =
      Zls.diagPow k N (fun i => w (blk (stdBlocks d hd) i)) := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  rw [coe_diagPow]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hij : i = j
    · subst hij
      rw [coe_zLevi, Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, blk_apply]
    · have hne := stdBlocks_ne d hd i j (fun e => hij (by simpa using e))
      rw [Matrix.diagonal_apply_ne _ hne, coe_zLevi, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
  · have hne := stdBlocks_ne d hd i j (fun e => hab (congrArg Sigma.fst e))
    rw [leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ hne]

def lam (d : Fin h → ℕ) (hd : ∑ a, d a = N) : Fin N → ℤ :=
  fun i => -(((blk (stdBlocks d hd) i : Fin h) : ℕ) : ℤ)

theorem one_block (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) (i j : Fin (d a)) :
    (1 : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩) =
      (1 : Matrix (Fin (d a)) (Fin (d a)) k) i j := by
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Matrix.one_apply_ne hij,
      Matrix.one_apply_ne (stdBlocks_ne d hd i j (fun e => hij (by simpa using e)))]

theorem unip_entries (d : Fin h → ℕ) (hd : ∑ a, d a = N) (y : GL (Fin N) k)
    (hy : y ∈ unipRad k (stdBlocks d hd)) (i j : Fin N) (hl : lam d hd i ≤ lam d hd j) :
    (y : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  have hab : b ≤ a := by
    simp only [lam, blk_apply, neg_le_neg_iff, Nat.cast_le] at hl
    exact hl
  obtain ⟨hp, hdg⟩ := mem_unipRad.1 hy
  rcases hab.eq_or_lt with rfl | hlt
  · rw [hdg, one_block]
  · rw [mem_parab_iff.1 hp a b i j hlt,
      Matrix.one_apply_ne (stdBlocks_ne d hd i j (fun e => hlt.ne' (congrArg Sigma.fst e)))]

theorem unipLower_entries (d : Fin h → ℕ) (hd : ∑ a, d a = N) (y : GL (Fin N) k)
    (hy : y ∈ unipRadLower k (stdBlocks d hd)) (i j : Fin N) (hl : (-lam d hd) i ≤ (-lam d hd) j) :
    (y : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks d hd).surjective j
  have hab : a ≤ b := by
    simp only [lam, Pi.neg_apply, blk_apply, neg_neg, Nat.cast_le] at hl
    exact hl
  obtain ⟨hp, hdg⟩ := (mem_unipRadLower k).1 hy
  rcases hab.eq_or_lt with rfl | hlt
  · rw [hdg, one_block]
  · rw [(mem_parabLower_iff k).1 hp a b i j hlt,
      Matrix.one_apply_ne (stdBlocks_ne d hd i j (fun e => hlt.ne (congrArg Sigma.fst e)))]

theorem exists_central_strictlyDominant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∃ a : Levi k (Bl d), (∀ x : Levi k (Bl d), a * x = x * a) ∧ IsStrictlyDominant k N J d hd a ∧ ∀ U : Set (GL (Fin N) k), IsOpen U → (1 : GL (Fin N) k) ∈ U → ∃ j : ℕ, ∀ y ∈ KNl k N J d hd, (leviEmb k (stdBlocks d hd) a ^ j)⁻¹ * y * leviEmb k (stdBlocks d hd) a ^ j ∈ U := by
  intro k _ _ _ _ N h d hd J hJo hJc _ _
  have hc := fun (l : Fin N → ℤ) S hS U hU h1 => exists_contract (k := k) l J hJc S hS U hU h1
  obtain ⟨c₁, hc₁⟩ := hc (lam d hd) (unipRad k (stdBlocks d hd)) (unip_entries d hd) J hJo J.one_mem
  obtain ⟨c₂, hc₂⟩ := hc (-lam d hd) (unipRadLower k (stdBlocks d hd)) (unipLower_entries d hd) J hJo
    J.one_mem
  obtain ⟨c, hc1, hcc₁, hcc₂⟩ : ∃ c : ℕ, 1 ≤ c ∧ c₁ ≤ c ∧ c₂ ≤ c :=
    ⟨max c₁ c₂ + 1, by omega, by omega, by omega⟩
  let a : Levi k (Bl d) := zLevi d ((c : ℤ) • fun b : Fin h => -((b : ℕ) : ℤ))
  have hemb : leviEmb k (stdBlocks d hd) a = Zls.diagPow k N ((c : ℤ) • lam d hd) :=
    leviEmb_zLevi d hd _
  have hpow : ∀ j : ℕ, leviEmb k (stdBlocks d hd) a ^ j =
      Zls.diagPow k N (((j * c : ℕ) : ℤ) • lam d hd) := by
    intro j
    rw [hemb, diagPow_pow, smul_smul]
    push_cast
    rfl
  have hinv : ∀ j : ℕ, Zls.diagPow k N (((j * c : ℕ) : ℤ) • (-lam d hd)) =
      (leviEmb k (stdBlocks d hd) a ^ j)⁻¹ := by
    intro j
    rw [smul_neg, diagPow_neg, hpow]
  have hemb' : Zls.diagPow k N ((c : ℤ) • (-lam d hd)) = (leviEmb k (stdBlocks d hd) a)⁻¹ := by
    rw [smul_neg, diagPow_neg, hemb]
  have hcent : ∀ x : Levi k (Bl d), a * x = x * a := zLevi_comm d _
  refine ⟨a, hcent, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro n hn
    refine ⟨?_, ?_⟩
    · rw [hemb]
      exact hc₁ c hcc₁ n hn.1 hn.2
    · exact (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k _ a) n).1 hn.2
  · intro n hn
    refine ⟨?_, ?_⟩
    · have := hc₂ c hcc₂ n hn.1 hn.2
      rwa [hemb', inv_inv] at this
    · have := (Subgroup.mem_normalizer_iff.1
        (inv_mem (leviEmb_mem_normalizer_lower k (stdBlocks d hd) a)) n).1 hn.2
      rwa [inv_inv] at this
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [hcent x, mul_inv_cancel_right]
      exact hx
    · rw [mul_assoc, ← hcent x, inv_mul_cancel_left]
      exact hx
  · intro U hU h1
    obtain ⟨c₃, hc₃⟩ := hc (lam d hd) (unipRad k (stdBlocks d hd)) (unip_entries d hd) U hU h1
    refine ⟨c₃, fun n hn => ?_⟩
    rw [hpow]
    exact hc₃ _ (Nat.le_mul_of_pos_right _ hc1) n hn.1 hn.2
  · intro U hU h1
    obtain ⟨c₃, hc₃⟩ := hc (-lam d hd) (unipRadLower k (stdBlocks d hd)) (unipLower_entries d hd) U hU h1
    refine ⟨c₃, fun y hy => ?_⟩
    have := hc₃ _ (Nat.le_mul_of_pos_right _ hc1) y hy.1 hy.2
    rwa [hinv, inv_inv] at this

end GlobalTheory.CompanionTheory.CentralDom
end
end

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_strictly_dominant_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∃ a : Levi k (Bl d), (∀ x : Levi k (Bl d), a * x = x * a) ∧ IsStrictlyDominant k N J d hd a ∧ ∀ U : Set (GL (Fin N) k), IsOpen U → (1 : GL (Fin N) k) ∈ U → ∃ j : ℕ, ∀ y ∈ KNl k N J d hd, (leviEmb k (stdBlocks d hd) a ^ j)⁻¹ * y * leviEmb k (stdBlocks d hd) a ^ j ∈ U := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CentralDom.exists_central_strictlyDominant
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

noncomputable section

namespace GlobalTheory.CompanionTheory.JacquetLemma

def cosetStab {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (q : Submodule ℂ V) (u : V) : Subgroup G where
  carrier := {x | ∀ v, π x v - u ∈ q ↔ v - u ∈ q}
  mul_mem' := by
    intro a b ha hb v
    rw [map_mul, Module.End.mul_apply, ha, hb]
  one_mem' := by intro v; simp
  inv_mem' := by
    intro a ha v
    have := ha (π a⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    exact this.symm

theorem mem_of_pow_mem {Q : Type} [AddCommGroup Q] [Module ℂ Q] (S : Submodule ℂ Q)
    [FiniteDimensional ℂ S] (A : Module.End ℂ Q) (hA : Function.Injective A)
    (hS : ∀ x ∈ S, A x ∈ S) (j : ℕ) (w : Q) (hw : (A ^ j) w ∈ S) : w ∈ S := by
  have step : ∀ x, A x ∈ S → x ∈ S := by
    intro x hx
    let B : S →ₗ[ℂ] S := LinearMap.restrict A hS
    have hB : Function.Injective B := by
      intro p q h
      apply Subtype.ext
      apply hA
      exact congrArg Subtype.val h
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hB) ⟨A x, hx⟩
    have h2 : A y = A x := congrArg Subtype.val hy
    rw [← hA h2]
    exact y.2
  induction j with
  | zero => simpa using hw
  | succ n ih =>
    apply ih
    apply step
    rw [← Module.End.mul_apply, ← pow_succ']
    exact hw

theorem exists_fixed_lift {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (J L A : Subgroup G) (hJo : IsOpen (J : Set G))
    (hJc : IsCompact (J : Set G)) (π : Representation ℂ G V) (hπ : IsSmooth π)
    (q : Submodule ℂ V) (u : V) (hLJ : L ≤ J) (hLu : ∀ y ∈ L, π y u = u) (hAJ : A ≤ J)
    (hAq : ∀ x ∈ A, π x u - u ∈ q) (hfact : ∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ L) :
    ∃ v ∈ fixed π J, v - u ∈ q :=
  _root_.UpperTheory.Reformulated.B.Gwa5.exists_fixed_lift J L A hJo hJc π hπ q u hLJ hLu hAJ hAq hfact

theorem rep_injective {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) : Function.Injective (ρ g) := by
  intro x y h
  have := congrArg (ρ g⁻¹) h
  simpa [← Module.End.mul_apply, ← map_mul] using this

end GlobalTheory.CompanionTheory.JacquetLemma

namespace GlobalTheory.CompanionTheory.JacquetLemma

theorem jacquet_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsAdmissible π → ∀ w ∈ fixed (jac (stdBlocks d hd) π) (KM k N J d hd), ∃ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = w := by
  intro k _ _ _ _ N h d hd J hJo hJc hI hpos V _ _ π hπ w hw
  obtain ⟨a, hac, hstrict, hshrink⟩ := GlobalTheory.T.central_strictly_dominant_exists k N h d hd J hJo hJc hI hpos
  obtain ⟨T, hT⟩ := GlobalTheory.T.jacquet_hecke_condition_holds k N J hJo hJc V π hπ.1 (leviEmb k (stdBlocks d hd) a)
  have hC2 := GlobalTheory.T.jacquet_hecke_compat_holds k N h d hd J hJo hJc hI hpos V π hπ.1 a hstrict.1 T hT
  haveI : FiniteDimensional ℂ (fixed π J) := hπ.2 J hJo hJc
  set q := twKer π (unipRad k (stdBlocks d hd)) 1 with hq
  let p : fixed π J →ₗ[ℂ] (V ⧸ q) := q.mkQ.comp (fixed π J).subtype
  let S : Submodule ℂ (V ⧸ q) := LinearMap.range p
  haveI : FiniteDimensional ℂ S := inferInstanceAs (FiniteDimensional ℂ (LinearMap.range p))
  let A : Module.End ℂ (V ⧸ q) := jac (stdBlocks d hd) π a
  have hAinj : Function.Injective A := rep_injective _ a
  have hAS : ∀ x ∈ S, A x ∈ S := by
    rintro _ ⟨v, rfl⟩
    refine ⟨(((deltaHalf k (Bl d) a : ℂˣ) : ℂ)⁻¹) • T v, ?_⟩
    have h1 := hC2 v
    show (Submodule.Quotient.mk (((((deltaHalf k (Bl d) a : ℂˣ) : ℂ)⁻¹) • T v : fixed π J) : V) : V ⧸ q) = A (Submodule.Quotient.mk (v : V))
    rw [Submodule.coe_smul, Submodule.Quotient.mk_smul, h1, smul_smul,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  obtain ⟨j, hj⟩ := hshrink {x | π x u = u} (hπ.1 u) (by simp)
  set g := leviEmb k (stdBlocks d hd) a with hg
  set u' : V := π (g ^ j) u with hu'

  have hpow : (A ^ j) (Submodule.Quotient.mk u) =
      (((deltaHalf k (Bl d) (a ^ j))⁻¹ : ℂˣ) : ℂ) • (Submodule.Quotient.mk u' : V ⧸ q) := by
    have h1 : A ^ j = jac (stdBlocks d hd) π (a ^ j) := (map_pow (jac (stdBlocks d hd) π) a j).symm
    have h2 : leviEmb k (stdBlocks d hd) (a ^ j) = g ^ j := map_pow _ _ _
    rw [h1, jac_mk, h2]

  have hLu : ∀ y ∈ KNl k N J d hd, π y u' = u' := by
    intro y hy
    have h2 : π ((g ^ j)⁻¹ * y * g ^ j) u = u := hj y hy
    have h3 : y * g ^ j = g ^ j * ((g ^ j)⁻¹ * y * g ^ j) := by group
    rw [hu', ← Module.End.mul_apply, ← map_mul, h3, map_mul, Module.End.mul_apply, h2]

  have hM : ∀ m ∈ KM k N J d hd, π (leviEmb k (stdBlocks d hd) m) u' - u' ∈ q := by
    intro m hm
    have h1 : jac (stdBlocks d hd) π m (Submodule.Quotient.mk u) = Submodule.Quotient.mk u := by
      have := hw ⟨m, hm⟩
      simpa using this
    rw [jac_mk, GlobalTheory.T.modulus_trivial_on_levi_compact k N h d hd J hJc m hm] at h1
    simp only [inv_one, Units.val_one, one_smul] at h1
    have h2 : (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) u) : V ⧸ q) = Submodule.Quotient.mk u := h1
    have h3 : jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) u)) =
        jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk u) := congrArg _ h2
    have h4 : (Submodule.Quotient.mk (π (g ^ j) (π (leviEmb k (stdBlocks d hd) m) u)) : V ⧸ q) = Submodule.Quotient.mk u' := by
      have e1 : ∀ z : V, jacU (stdBlocks d hd) π (a ^ j) (Submodule.Quotient.mk z) = (Submodule.Quotient.mk (π (g ^ j) z) : V ⧸ q) := by
        intro z
        rw [hg, ← map_pow]
        rfl
      rw [e1, e1] at h3
      exact h3
    have hcomm : leviEmb k (stdBlocks d hd) m * g ^ j = g ^ j * leviEmb k (stdBlocks d hd) m := by
      have : m * a ^ j = a ^ j * m := ((Commute.pow_right (show Commute m a from (hac m).symm) j))
      have := congrArg (leviEmb k (stdBlocks d hd)) this
      simpa [map_mul, map_pow, hg] using this
    rw [← Submodule.Quotient.eq, hu', ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    exact h4
  have hMstab : ∀ m ∈ KM k N J d hd, leviEmb k (stdBlocks d hd) m ∈ cosetStab π q u' := by
    intro m hm v
    have h1 := hM m hm
    have hinj := rep_injective (jacU (stdBlocks d hd) π) m
    have e1 : ∀ z : V, jacU (stdBlocks d hd) π m (Submodule.Quotient.mk z) = (Submodule.Quotient.mk (π (leviEmb k (stdBlocks d hd) m) z) : V ⧸ q) := fun z => rfl
    rw [← Submodule.Quotient.eq] at h1 ⊢
    rw [← Submodule.Quotient.eq, ← e1]
    conv_lhs => rw [← h1, ← e1]
    exact hinj.eq_iff
  have hNstab : ∀ c ∈ unipRad k (stdBlocks d hd), c ∈ cosetStab π q u' := by
    intro c hc v
    have h1 : π c v - v ∈ q := by
      refine Submodule.subset_span ⟨⟨c, hc⟩, v, ?_⟩
      simp
    rw [← Submodule.Quotient.eq, ← Submodule.Quotient.eq, (Submodule.Quotient.eq q).2 h1]
  obtain ⟨v, hv, hvu⟩ := exists_fixed_lift J (KNl k N J d hd) (J ⊓ cosetStab π q u') hJo hJc π hπ.1 q u'
    inf_le_left hLu inf_le_left
    (fun x hx => by
      have := (hx.2 u').2 (by simp)
      exact this)
    (fun y hy => by
      obtain ⟨a', ha', b, hb, c, hc, hy'⟩ := hI y⁻¹ (inv_mem hy)
      obtain ⟨m, hm⟩ := hb.2
      have hmK : m ∈ KM k N J d hd := by
        show leviEmb k (stdBlocks d hd) m ∈ J
        rw [hm]; exact hb.1
      have hbS : b ∈ cosetStab π q u' := hm ▸ hMstab m hmK
      refine ⟨c⁻¹ * b⁻¹, ⟨J.mul_mem (J.inv_mem hc.1) (J.inv_mem hb.1),
        (cosetStab π q u').mul_mem ((cosetStab π q u').inv_mem (hNstab c hc.2)) ((cosetStab π q u').inv_mem hbS)⟩, ?_⟩
      have h5 : (c⁻¹ * b⁻¹)⁻¹ * y = a'⁻¹ := by
        have : y = (a' * b * c)⁻¹ := by rw [← hy']; simp
        rw [this]; group
      rw [h5]
      exact inv_mem ha')
  have hS' : (Submodule.Quotient.mk u' : V ⧸ q) ∈ S :=
    ⟨⟨v, hv⟩, (Submodule.Quotient.eq q).2 hvu⟩
  have hmem : (Submodule.Quotient.mk u : V ⧸ q) ∈ S := by
    refine mem_of_pow_mem S A hAinj hAS j _ ?_
    rw [hpow]
    exact S.smul_mem _ hS'
  obtain ⟨v', hv'⟩ := hmem
  exact ⟨v', hv'⟩

end GlobalTheory.CompanionTheory.JacquetLemma
end
end

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_fixed_vector_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsAdmissible π → ∀ w ∈ fixed (jac (stdBlocks d hd) π) (KM k N J d hd), ∃ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = w := by
  atlas_forward_decl GlobalTheory.CompanionTheory.JacquetLemma.jacquet_surjective
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem mk_mem_fixed_jac : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) ∈ fixed (jac (stdBlocks d hd) π) (KM k N J d hd) := by
  intro k _ _ _ _ N h d hd J _ hc _ _ V _ _ π _ v x
  have hx : leviEmb k (stdBlocks d hd) (x : Levi k (Bl d)) ∈ J := x.2
  have hv : π (leviEmb k (stdBlocks d hd) (x : Levi k (Bl d))) (v : V) = (v : V) := by
    simpa using v.2 ⟨_, hx⟩
  have hδ : deltaHalf k (Bl d) (x : Levi k (Bl d)) = 1 := GlobalTheory.T.modulus_trivial_on_levi_compact k N h d hd J hc x x.2
  rw [jac_mk, hv, hδ]
  simp

end GlobalTheory.CompanionTheory.Casselman
end

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_projection_fixed_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) ∈ fixed (jac (stdBlocks d hd) π) (KM k N J d hd) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Casselman.mk_mem_fixed_jac
end

section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem isDominant_one_and_mul :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (J : Subgroup (GL (Fin N) k)) (h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N),
      IsDominant k N J d hd 1 ∧ ∀ t t' : Levi k (Bl d), IsDominant k N J d hd t →
        IsDominant k N J d hd t' → IsDominant k N J d hd (t * t') := by
  intro k _ _ _ _ N J h d hd
  refine ⟨⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ?_⟩, ?_⟩
  · simpa using hn
  · simpa using hn
  · simpa using hx
  · rintro t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩
    · have key := h1 _ (h1' n hn)
      rw [map_mul]
      convert key using 1
      group
    · have key := h2' _ (h2 n hn)
      rw [map_mul]
      convert key using 1
      group
    · have key := (h3 _ (h3' x hx).1).1
      convert key using 1
      group
    · have key := (h3' _ (h3 x hx).2).2
      convert key using 1
      group

end GlobalTheory.CompanionTheory.Lbc
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem hecke_dominant_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hIw hpos V _ _ π hπ t t' ht ht' T T' hT hT' v l hl
  obtain ⟨r, hr, x, hxN, hx⟩ := GlobalTheory.T.dominant_iwahori_coset_reps k N h d hd J hJo hJc hIw hpos t' ht'
  have hxJ : ∀ i, x i ∈ J := fun i => (hxN i).1
  have hform := GlobalTheory.T.hecke_operator_coset_sum k N J hJc V π hπ _ T' hT' r x hr hxJ hx v
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  set g := leviEmb k (stdBlocks d hd) t with hg
  set g' := leviEmb k (stdBlocks d hd) t' with hg'
  have hmul : leviEmb k (stdBlocks d hd) (t * t') = g * g' := map_mul _ _ _
  have hterm : ∀ i, l (π g (π (x i * g') (v : V))) = l (π (g * g') (v : V)) := by
    intro i
    have hc : g * x i * g⁻¹ ∈ J := (ht.1 _ (hxN i)).1
    have hfac : g * (x i * g') = (g * x i * g⁻¹) * (g * g') := by group
    have h1 : l (π (g * x i * g⁻¹) (π (g * g') (v : V))) = l (π (g * g') (v : V)) :=
      LinearMap.congr_fun (hl _ hc) _
    rw [← Module.End.mul_apply, ← map_mul, hfac, map_mul, Module.End.mul_apply, h1]
  have hTT : l (((T * T') v : fixed π J) : V) = l (π g ((T' v : fixed π J) : V)) :=
    (hT (T' v) l hl).symm
  rw [hTT, hform, hmul, map_smul, map_sum, map_smul, map_sum]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [smul_eq_mul]
  field_simp

end GlobalTheory.CompanionTheory.Lbc
end

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_fixed_first_condition : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C1 k := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Lbc.hecke_dominant_mul
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc Topology Filter Matrix

namespace GlobalTheory.CompanionTheory.ExpandN

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nhdsNE_zero_neBot : (𝓝[≠] (0 : k)).NeBot := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedField.nhdsNE_neBot (0 : k)

theorem exists_one_add_smul_mem_unipRad {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (Σ a, m a) ≃ n) {u : GL n k} (hu : u ∈ unipRad k e) (c : k) :
    ∃ v : GL n k, (v : Matrix n n k) = 1 + c • ((u : Matrix n n k) - 1) ∧ v ∈ unipRad k e := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hu
  have hsame : ∀ i j, blk e i = blk e j → (u : Matrix n n k) i j = (1 : Matrix n n k) i j := by
    intro i j hij
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    obtain rfl : a = b := by simpa using hij
    rw [hD a i j, Matrix.one_apply, Matrix.one_apply]
    simp
  set M : Matrix n n k := 1 + c • ((u : Matrix n n k) - 1) with hM
  have hMsame : ∀ i j, blk e i = blk e j → M i j = (1 : Matrix n n k) i j := by
    intro i j hij
    simp [hM, hsame i j hij]
  have hT : M.BlockTriangular (blk e) := by
    intro i j hij
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    have h0 : (u : Matrix n n k) i j = 0 := mem_parab.1 hP i j hij
    simp [hM, h0, Matrix.one_apply_ne hne]
  have hdet : M.det = 1 := by
    rw [hT.det_fintype]
    refine Finset.prod_eq_one fun a _ => ?_
    have : M.toSquareBlock (blk e) a = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      rw [Matrix.toSquareBlock_def]
      simp only [Matrix.of_apply]
      rw [hMsame i j (hi.trans hj.symm), Matrix.one_apply, Matrix.one_apply]
      simp
    rw [this, Matrix.det_one]
  obtain ⟨v, hv⟩ : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by simp [hdet])
  refine ⟨v, hv, mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩⟩
  · rw [hv]; exact hT hij
  · rw [hv, hMsame _ _ (by simp), Matrix.one_apply, Matrix.one_apply]
    simp

theorem val_conj_one_add_smul {n : Type} [Fintype n] [DecidableEq n] (G u v : GL n k) (c : k)
    (hv : (v : Matrix n n k) = 1 + c • ((u : Matrix n n k) - 1)) :
    ((G * v * G⁻¹ : GL n k) : Matrix n n k) =
      1 + c • (((G * u * G⁻¹ : GL n k) : Matrix n n k) - 1) := by
  have h1 : (G : Matrix n n k) * ((G⁻¹ : GL n k) : Matrix n n k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul, hv, mul_add, add_mul, mul_sub, sub_mul, mul_one,
    Matrix.mul_smul, Matrix.smul_mul, h1]

theorem exists_pow_conj_mem_KN : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) →
    IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t →
    ∀ n ∈ unipRad k (stdBlocks d hd), ∃ r : ℕ,
      leviEmb k (stdBlocks d hd) t ^ r * n * (leviEmb k (stdBlocks d hd) t ^ r)⁻¹ ∈ KN k N J d hd := by
  intro k _ _ _ _ N h d hd J hJo _ _ _ t ht n hn
  obtain ⟨O, hO, hOJ⟩ := (GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := Fin N)).isInducing.isOpen_iff.1 hJo
  have memJ : ∀ x : GL (Fin N) k, x ∈ J ↔ (x : Matrix (Fin N) (Fin N) k) ∈ O := by
    intro x
    have : x ∈ (J : Set (GL (Fin N) k)) ↔ x ∈ (fun g : GL (Fin N) k => g.val) ⁻¹' O := by rw [hOJ]
    exact this
  have h1O : (1 : Matrix (Fin N) (Fin N) k) ∈ O := by
    simpa using (memJ 1).1 J.one_mem
  set X : Matrix (Fin N) (Fin N) k := (n : Matrix (Fin N) (Fin N) k) - 1 with hX
  haveI := nhdsNE_zero_neBot (k := k)
  have hcont : Continuous fun c : k => (1 : Matrix (Fin N) (Fin N) k) + c • X :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hev : ∀ᶠ c in 𝓝[≠] (0 : k), (1 : Matrix (Fin N) (Fin N) k) + c • X ∈ O := by
    have : ∀ᶠ c in 𝓝 (0 : k), (1 : Matrix (Fin N) (Fin N) k) + c • X ∈ O :=
      hcont.continuousAt.eventually_mem (hO.mem_nhds (by simpa using h1O))
    exact this.filter_mono nhdsWithin_le_nhds
  obtain ⟨c, hcO, hc0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hc0' : c ≠ 0 := hc0
  obtain ⟨v, hv, hvN⟩ := exists_one_add_smul_mem_unipRad (stdBlocks d hd) hn c
  have hvJ : v ∈ J := (memJ v).2 (by rw [hv]; exact hcO)
  let U : Set (GL (Fin N) k) := (fun g : GL (Fin N) k =>
    (1 : Matrix (Fin N) (Fin N) k) + c⁻¹ • ((g : Matrix (Fin N) (Fin N) k) - 1)) ⁻¹' O
  have hU : IsOpen U := by
    refine hO.preimage ?_
    have hs : Continuous fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) - 1 :=
      Units.continuous_val.sub continuous_const
    exact continuous_const.add (hs.const_smul c⁻¹)
  have h1U : (1 : GL (Fin N) k) ∈ U := by
    show (1 : Matrix (Fin N) (Fin N) k) + c⁻¹ • (((1 : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1) ∈ O
    simpa using h1O
  obtain ⟨j, hj⟩ := ht.2 U hU h1U
  refine ⟨j, ?_⟩
  set G := leviEmb k (stdBlocks d hd) t ^ j with hG
  have hGn : G ∈ Subgroup.normalizer (unipRad k (stdBlocks d hd) : Set (GL (Fin N) k)) :=
    pow_mem (leviEmb_mem_normalizer k (stdBlocks d hd) t) j
  have hmem := hj v (Subgroup.mem_inf.2 ⟨hvJ, hvN⟩)
  have hval := val_conj_one_add_smul G n v c hv
  refine Subgroup.mem_inf.2 ⟨(memJ _).2 ?_, (Subgroup.mem_normalizer_iff.1 hGn n).1 hn⟩
  have hmem' : (1 : Matrix (Fin N) (Fin N) k) +
      c⁻¹ • (((G * v * G⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1) ∈ O := hmem
  rw [hval] at hmem'
  simpa [smul_smul, inv_mul_cancel₀ hc0'] using hmem'

end GlobalTheory.CompanionTheory.ExpandN
end

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictly_dominant_contracts_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ n ∈ unipRad k (stdBlocks d hd), ∃ r : ℕ, leviEmb k (stdBlocks d hd) t ^ r * n * (leviEmb k (stdBlocks d hd) t ^ r)⁻¹ ∈ KN k N J d hd := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ExpandN.exists_pow_conj_mem_KN
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem heckeOp_nilpotent_on_ker :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ T : Module.End ℂ (fixed π J), IsHeckeOp π J (leviEmb k (stdBlocks d hd) t) T → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = 0 → ∃ r : ℕ, (T ^ r) v = 0 := by
  intro k _ _ _ _ N h d hd J hJo hJc hJf hpos V _ _ π hπ t ht T hT v hv
  set e := leviEmb k (stdBlocks d hd) with he

  have hdom : ∀ r : ℕ, IsDominant k N J d hd (t ^ r) := by
    intro r
    induction r with
    | zero => simpa using (isDominant_one_and_mul k N J h d hd).1
    | succ r ih =>
      rw [pow_succ]
      exact (isDominant_one_and_mul k N J h d hd).2 _ _ ih ht.1

  have hecke : ∀ r : ℕ, IsHeckeOp π J (e (t ^ r)) (T ^ r) := by
    intro r
    induction r with
    | zero =>
      intro w l _
      simp
    | succ r ih =>
      rw [pow_succ, pow_succ T]
      exact GlobalTheory.T.jacquet_fixed_first_condition k N h d hd J hJo hJc hJf hpos V π hπ _ _ (hdom r) ht.1 _ _ ih hT

  have key : ∀ u ∈ twKer π (unipRad k (stdBlocks d hd)) 1, ∃ R : ℕ, ∀ r ≥ R,
      ∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l (π (e t ^ r) u) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨n, w, rfl⟩ := hu
      obtain ⟨R, hR⟩ := GlobalTheory.T.strictly_dominant_contracts_unipotent k N h d hd J hJo hJc hJf hpos t ht (n : GL (Fin N) k) n.2
      refine ⟨R, fun r hr l hl => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
      have hmem : e t ^ (R + j) * (n : GL (Fin N) k) * (e t ^ (R + j))⁻¹ ∈ KN k N J d hd := by
        have := (hdom j).1 _ hR
        rw [map_pow] at this
        convert this using 1
        rw [add_comm R j, pow_add]
        group
        rfl
      have hx := hl _ hmem.1
      have hy := LinearMap.congr_fun hx (π (e t ^ (R + j)) w)
      simp only [LinearMap.comp_apply] at hy
      have hz : π (e t ^ (R + j) * (n : GL (Fin N) k) * (e t ^ (R + j))⁻¹) (π (e t ^ (R + j)) w)
          = π (e t ^ (R + j)) (π (n : GL (Fin N) k) w) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [hz] at hy
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hy, sub_self]
    | zero => exact ⟨0, fun r _ l _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨A, hA⟩ := ha
      obtain ⟨B, hB⟩ := hb
      refine ⟨max A B, fun r hr l hl => ?_⟩
      rw [map_add, map_add, hA r (le_trans (le_max_left _ _) hr) l hl,
        hB r (le_trans (le_max_right _ _) hr) l hl, add_zero]
    | smul c a _ ha =>
      obtain ⟨A, hA⟩ := ha
      refine ⟨A, fun r hr l hl => ?_⟩
      rw [map_smul, map_smul, hA r hr l hl, smul_zero]
  obtain ⟨R, hR⟩ := key _ ((Submodule.Quotient.mk_eq_zero _).1 hv)
  refine ⟨R, ?_⟩
  have h0 : (((T ^ R) v : fixed π J) : V) = 0 := by
    refine GlobalTheory.T.fixed_vector_zero_of_dual _ J hJc V π hπ _ ((T ^ R) v).2 fun l hl => ?_
    rw [← hecke R v l hl, map_pow]
    exact hR R le_rfl l hl
  exact Subtype.ext h0

end GlobalTheory.CompanionTheory.Lbc
end

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictly_dominant_hecke_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ t : Levi k (Bl d), IsStrictlyDominant k N J d hd t → ∀ T : Module.End ℂ (fixed π J), IsHeckeOp π J (leviEmb k (stdBlocks d hd) t) T → ∀ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = 0 → ∃ r : ℕ, (T ^ r) v = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Lbc.heckeOp_nilpotent_on_ker
end

section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc

theorem c3 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.C3 k := by
  intro k _ _ _ _ N h d hd J hJo hJc hJf hpos V _ _ π hπ
  exact ⟨GlobalTheory.T.jacquet_projection_fixed_surjective k N h d hd J hJo hJc hJf hpos V π hπ.1,
    GlobalTheory.T.jacquet_fixed_vector_lift k N h d hd J hJo hJc hJf hpos V π hπ,
    GlobalTheory.T.strictly_dominant_hecke_kernel k N h d hd J hJo hJc hJf hpos V π hπ.1⟩

end GlobalTheory.CompanionTheory.Lbc
end
