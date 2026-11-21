import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DetAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SubMulAddEpM

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mem_ev_iff_apply_eq_zero_off_diagonal_blocks {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (n a : ℕ)
    (Z : Matrix (Fin n) (Fin n) R) :
    Z ∈ Ev A R n a ↔ ∀ i j : Fin n, ¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j = 0 := by
  constructor
  · intro h i j hij
    exact (Submodule.mem_bot A).1 ((h i j).2 hij)
  · intro h i j
    exact ⟨fun _ => Submodule.mem_top, fun hij => by rw [h i j hij]; exact Submodule.zero_mem _⟩

theorem UpperTheory.V.Pa.Det.detFr :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n), l ≠ 2 → (∃ g : F.G₀, PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → ∃ D : DetFr (FractionRing x.A) F.G₀ n, D.a = x.a ∧ D.G' = F.G' ∧ (∀ g, D.r g = x.ρX (FractionRing x.A) g) ∧ D.σ = F.conj ∧ ∀ g : F.G₀, D.χF g = algebraMap x.A (FractionRing x.A) (algebraMap ℤ_[l] x.A (F.ε g : ℤ_[l])) := by
  intro l _ F n x hl hg
  obtain ⟨g₀, hg₀⟩ := hg
  have hev : ∀ g : F.G₀, (mat x.ρ g).map (algebraMap x.A (FractionRing x.A)) ∈
      Ev (FractionRing x.A) (FractionRing x.A) n x.a := by
    intro g
    rw [mem_ev_iff_apply_eq_zero_off_diagonal_blocks]
    intro i j hij
    have h0 := (mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 (x.blk g) i j hij
    rw [Matrix.map_apply, h0, map_zero]
  have hmap : ∀ M ∈ Submodule.span x.A ((mat x.ρ) '' (F.G' : Set F.G₀)),
      M.map (algebraMap x.A (FractionRing x.A)) ∈ Submodule.span (FractionRing x.A)
        ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      exact Submodule.subset_span ⟨g, hg, rfl⟩
    | zero =>
      have h0 : (0 : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A (FractionRing x.A)) = 0 := by
        ext i j
        simp
      rw [h0]
      exact Submodule.zero_mem _
    | add M N _ _ hM hN =>
      have h0 : (M + N).map (algebraMap x.A (FractionRing x.A)) =
          M.map (algebraMap x.A (FractionRing x.A)) + N.map (algebraMap x.A (FractionRing x.A)) := by
        ext i j
        simp
      rw [h0]
      exact Submodule.add_mem _ hM hN
    | smul c M _ hM =>
      have h0 : (c • M).map (algebraMap x.A (FractionRing x.A)) =
          algebraMap x.A (FractionRing x.A) c • M.map (algebraMap x.A (FractionRing x.A)) := by
        ext i j
        simp
      rw [h0]
      exact Submodule.smul_mem _ _ hM
  have hsingle : ∀ i j : Fin n, ((i : ℕ) < x.a ↔ (j : ℕ) < x.a) →
      Matrix.single i j (1 : FractionRing x.A) ∈ Submodule.span (FractionRing x.A)
        ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) := by
    intro i j hij
    have hZ : Matrix.single i j (1 : x.A) ∈ Ev x.A x.A n x.a := by
      rw [mem_ev_iff_apply_eq_zero_off_diagonal_blocks]
      intro k m hkm
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hkm hij
    obtain ⟨s, hs⟩ := x.span _ hZ
    have key := hmap _ hs
    have h1 : ((PowerSeries.X : x.A) ^ s • Matrix.single i j (1 : x.A)).map
        (algebraMap x.A (FractionRing x.A)) =
        algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) • Matrix.single i j (1 : FractionRing x.A) := by
      ext k m
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [h1] at key
    have hne : algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) ≠ 0 := by
      intro h
      apply pow_ne_zero s (PowerSeries.X_ne_zero (R := x.K))
      apply IsFractionRing.injective x.A (FractionRing x.A)
      rw [h, map_zero]
    have h2 := Submodule.smul_mem _ (algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s))⁻¹ key
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  have hspan : Submodule.span (FractionRing x.A)
      ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) =
      Ev (FractionRing x.A) (FractionRing x.A) n x.a := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, -, rfl⟩
      exact hev g
    · intro Z hZ
      rw [Matrix.matrix_eq_sum_single Z]
      refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_))
      by_cases hij : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)
      · have h3 : Matrix.single i j (Z i j) = Z i j • Matrix.single i j (1 : FractionRing x.A) := by
          rw [Matrix.smul_single, smul_eq_mul, mul_one]
        rw [h3]
        exact Submodule.smul_mem _ _ (hsingle i j hij)
      · rw [(mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 hZ i j hij, Matrix.single_zero]
        exact Submodule.zero_mem _
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra h
    have hm : (2 : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal _).2 h
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm
    have h4 : ((2 : ℕ) : ZMod l) = 0 := by
      rw [Nat.cast_ofNat, ← hm, map_ofNat]
    have h5 : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).1 h4
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h5)
  have hc : ∀ g : F.G₀, F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
    intro g
    show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = F.ε (g : F.Γ)
    rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_inv_cancel_right]
  refine ⟨DetFr.mk ?_ x.a x.a_pos x.a_le F.G' ?_ (F.eps x.A (FractionRing x.A)) ?_ g₀ ?_
    ((algebraMap x.A (FractionRing x.A)).mapMatrix.toMonoidHom.comp (mat x.ρ)) hspan hev F.conj ?_ ?_
    (fun g => Units.map (algebraMap x.A (FractionRing x.A)).toMonoidHom
      ((F.eps ℤ_[l] x.A g) ^ (1 - (n : ℤ)))) ?_, rfl, rfl, fun g => rfl, rfl, fun g => rfl⟩
  · have h6 := (h2.map ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A))).ne_zero
    rw [RingHom.comp_apply, map_ofNat, map_ofNat] at h6
    exact h6
  · intro g h
    rw [GFrame.G', MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul, mul_comm]
  · intro g hg
    rw [GFrame.G', MonoidHom.mem_ker] at hg
    show Units.map _ ((F.ε.comp F.η.ker.subtype) g) = 1
    rw [hg, map_one]
  · intro h
    apply hg₀
    have h7 := congrArg Units.val h
    change algebraMap x.A (FractionRing x.A) (algebraMap ℤ_[l] x.A ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l])) = 1 at h7
    have h8 : ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈
        RingHom.ker ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A)) := by
      rw [RingHom.mem_ker, map_sub, RingHom.comp_apply, h7, map_one, sub_self]
    have h9 := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) h8
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h9
    exact h9
  · intro g
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = (g : F.Γ)
    calc F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = (F.c * F.c) * (g : F.Γ) * (F.c * F.c)⁻¹ := by group
      _ = (g : F.Γ) := by rw [F.c_sq]; group
  · intro g
    show Units.map _ ((F.ε.comp F.η.ker.subtype) (F.conj g)) = Units.map _ ((F.ε.comp F.η.ker.subtype) g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact congrArg _ (hc g)
  · intro g
    show ((mat x.ρ g).map (algebraMap x.A (FractionRing x.A)))ᵀ *
        (mat x.ρ (F.conj g)).map (algebraMap x.A (FractionRing x.A)) =
        (algebraMap x.A (FractionRing x.A) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A)) • 1
    have h0 := x.form g
    rw [Units.val_one, Matrix.mul_one] at h0
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h0]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
end

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.w1sMem :
    ∀ {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}, (∀ Z : Matrix (Fin n) (Fin n) (DD X g), Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a → etaM Z ∈ Ev A X n a ∧ ∀ j, ep'M j Z ∈ Od A X n a) ∧ (∀ Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, ∀ Z' ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, etaM Z = etaM Z' → (∀ j, ep'M j Z = ep'M j Z') → Z = Z') ∧ ∀ (Y₀ : Matrix (Fin n) (Fin n) X) (Y : Fin g → Matrix (Fin n) (Fin n) X), Y₀ ∈ Ev A X n a → (∀ j, Y j ∈ Od A X n a) → ∃ Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a, etaM Z = Y₀ ∧ ∀ j, ep'M j Z = Y j := by
  intro A X _ _ _ g n a
  have hW : ∀ Z : Matrix (Fin n) (Fin n) (DD X g), Z ∈ pairedDualFirstOrderDualMatrixSpace n A X g a ↔ ∀ i j : Fin n,
      ((↑i < a ↔ ↑j < a) → (Z i j).a = 0 ∧ (Z i j).ep = 0 ∧ (Z i j).ep' = 0) ∧
      (¬(↑i < a ↔ ↑j < a) → (Z i j).a = 0 ∧ (Z i j).ep = 0 ∧ (Z i j).eta = 0) := by
    intro Z
    simp [pairedDualFirstOrderDualMatrixSpace, blkMat, ddPart]
  have hE : ∀ Y : Matrix (Fin n) (Fin n) X, Y ∈ Ev A X n a ↔
      ∀ i j : Fin n, ¬(↑i < a ↔ ↑j < a) → Y i j = 0 := by
    intro Y
    simp [Ev, blkMat]
  have hO : ∀ Y : Matrix (Fin n) (Fin n) X, Y ∈ Od A X n a ↔
      ∀ i j : Fin n, (↑i < a ↔ ↑j < a) → Y i j = 0 := by
    intro Y
    simp [Od, blkMat]
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ
    rw [hW] at hZ
    refine ⟨(hE _).2 fun i j hij => ((hZ i j).2 hij).2.2, fun l => (hO _).2 fun i j hij => ?_⟩
    simp only [ep'M, Matrix.map_apply]
    rw [((hZ i j).1 hij).2.2]
    rfl
  · intro Z hZ Z' hZ' he hp
    rw [hW] at hZ hZ'
    funext i j
    have h1 := congrFun (congrFun he i) j
    have h2 : ∀ l, (Z i j).ep' l = (Z' i j).ep' l := fun l => congrFun (congrFun (hp l) i) j
    simp only [etaM, Matrix.map_apply] at h1
    have ha : (Z i j).a = (Z' i j).a ∧ (Z i j).ep = (Z' i j).ep := by
      by_cases hij : (↑i < a ↔ ↑j < a)
      · rw [((hZ i j).1 hij).1, ((hZ' i j).1 hij).1, ((hZ i j).1 hij).2.1, ((hZ' i j).1 hij).2.1]
        exact ⟨rfl, rfl⟩
      · rw [((hZ i j).2 hij).1, ((hZ' i j).2 hij).1, ((hZ i j).2 hij).2.1, ((hZ' i j).2 hij).2.1]
        exact ⟨rfl, rfl⟩
    exact DD.ext ha.1 ha.2 (funext h2) h1
  · intro Y₀ Y h0 hY
    rw [hE] at h0
    refine ⟨Matrix.of fun i j => ⟨0, 0, fun l => Y l i j, Y₀ i j⟩, (hW _).2 fun i j =>
      ⟨fun hij => ⟨rfl, rfl, funext fun l => (hO _).1 (hY l) i j hij⟩, fun hij => ⟨rfl, rfl, h0 i j hij⟩⟩,
      rfl, fun l => rfl⟩
end

section
noncomputable section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa.Det

section Comp

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

variable (P Q : Matrix (Fin n) (Fin n) (DD X g))

variable (M : Matrix (Fin n) (Fin n) A) (K : Fin g → Matrix (Fin n) (Fin n) X)

variable {N N' : Matrix (Fin n) (Fin n) X}

variable {M}

variable {P}

end Comp

end UpperTheory.V.Pa.Det

open IsLocalRing UpperTheory.V.Pa

private theorem dd_eta_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ m ∈ s, f m).eta = ∑ m ∈ s, (f m).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_eta]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_eta, ih]

private theorem dd_a_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ m ∈ s, f m).a = ∑ m ∈ s, (f m).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_a]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_a, ih]

private theorem dd_ep_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (j : Fin g) :
    (∑ m ∈ s, f m).ep j = ∑ m ∈ s, (f m).ep j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_ep]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_ep, ih]

private theorem dd_ep'_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (j : Fin g) :
    (∑ m ∈ s, f m).ep' j = ∑ m ∈ s, (f m).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_ep']
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_ep', ih]

private theorem matrix_map_dd_a_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P * Q).map DD.a = P.map DD.a * Q.map DD.a := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, dd_a_sum, DD.mul_a]

private theorem matrix_map_dd_ep_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) (j : Fin g) :
    (P * Q).map (fun d => d.ep j) = P.map DD.a * Q.map (fun d => d.ep j) + P.map (fun d => d.ep j) * Q.map DD.a := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, dd_ep_sum, DD.mul_ep, Finset.sum_add_distrib]

private theorem matrix_map_dd_ep'_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) (j : Fin g) :
    (P * Q).map (fun d => d.ep' j) = P.map DD.a * Q.map (fun d => d.ep' j) + P.map (fun d => d.ep' j) * Q.map DD.a := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, dd_ep'_sum, DD.mul_ep', Finset.sum_add_distrib]

private theorem matrix_map_dd_eta_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P * Q).map DD.eta = P.map DD.a * Q.map DD.eta + P.map DD.eta * Q.map DD.a +
      ∑ j, (P.map (fun d => d.ep j) * Q.map (fun d => d.ep' j) + P.map (fun d => d.ep' j) * Q.map (fun d => d.ep j)) := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.sum_apply, dd_eta_sum, DD.mul_eta,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 2
  exact Finset.sum_comm

private theorem mul_apply_eq_zero_of_block_parity {X : Type} [CommRing X] {n a : ℕ} (p q : Prop) (P Q : Matrix (Fin n) (Fin n) X)
    (hP : ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ p) → P i j = 0)
    (hQ : ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ q) → Q i j = 0) :
    ∀ i k : Fin n, ¬(((i : ℕ) < a ↔ (k : ℕ) < a) ↔ (p ↔ q)) → (P * Q) i k = 0 := by
  intro i k h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases h1 : (((i : ℕ) < a ↔ (m : ℕ) < a) ↔ p)
  · have h2 : ¬(((m : ℕ) < a ↔ (k : ℕ) < a) ↔ q) := by tauto
    rw [hQ m k h2, mul_zero]
  · rw [hP i m h1, zero_mul]

private theorem ofPar_lemma {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ} (p : Prop)
    (P : Matrix (Fin n) (Fin n) X) :
    (P ∈ blkMat n a (⊤ : Submodule A X) ⊥ → ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ True) → P i j = 0) ∧
    (P ∈ blkMat n a (⊥ : Submodule A X) ⊤ → ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ False) → P i j = 0) ∧
    ((∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ True) → P i j = 0) → P ∈ blkMat n a (⊤ : Submodule A X) ⊥) ∧
    ((∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ False) → P i j = 0) → P ∈ blkMat n a (⊥ : Submodule A X) ⊤) := by
  refine ⟨fun h i j hij => ?_, fun h i j hij => ?_, fun h i j => ?_, fun h i j => ?_⟩
  · exact (Submodule.mem_bot A).1 ((h i j).2 (by tauto))
  · exact (Submodule.mem_bot A).1 ((h i j).1 (by tauto))
  · exact ⟨fun _ => Submodule.mem_top, fun hh => (Submodule.mem_bot A).2 (h i j (by tauto))⟩
  · exact ⟨fun hh => (Submodule.mem_bot A).2 (h i j (by tauto)), fun _ => Submodule.mem_top⟩

private theorem ev_od_graded_mul_mem {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ}
    (P Q : Matrix (Fin n) (Fin n) X) :
    (P ∈ Ev A X n a → Q ∈ Ev A X n a → P * Q ∈ Ev A X n a) ∧
    (P ∈ Ev A X n a → Q ∈ Od A X n a → P * Q ∈ Od A X n a) ∧
    (P ∈ Od A X n a → Q ∈ Ev A X n a → P * Q ∈ Od A X n a) ∧
    (P ∈ Od A X n a → Q ∈ Od A X n a → P * Q ∈ Ev A X n a) := by
  have c := ofPar_lemma (A := A) (X := X) (n := n) (a := a) True
  refine ⟨fun hP hQ => ?_, fun hP hQ => ?_, fun hP hQ => ?_, fun hP hQ => ?_⟩
  · exact (c (P * Q)).2.2.1 fun i k h =>
      mul_apply_eq_zero_of_block_parity True True P Q ((c P).1 hP) ((c Q).1 hQ) i k (by tauto)
  · exact (c (P * Q)).2.2.2 fun i k h =>
      mul_apply_eq_zero_of_block_parity True False P Q ((c P).1 hP) ((c Q).2.1 hQ) i k (by tauto)
  · exact (c (P * Q)).2.2.2 fun i k h =>
      mul_apply_eq_zero_of_block_parity False True P Q ((c P).2.1 hP) ((c Q).1 hQ) i k (by tauto)
  · exact (c (P * Q)).2.2.1 fun i k h =>
      mul_apply_eq_zero_of_block_parity False False P Q ((c P).2.1 hP) ((c Q).2.1 hQ) i k (by tauto)

private theorem map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ}
    (P : Matrix (Fin n) (Fin n) A) :
    (P ∈ Ev A A n a → P.map (algebraMap A X) ∈ Ev A X n a) ∧
    (P ∈ Od A A n a → P.map (algebraMap A X) ∈ Od A X n a) := by
  have c := ofPar_lemma (A := A) (X := A) (n := n) (a := a) True P
  have d := ofPar_lemma (A := A) (X := X) (n := n) (a := a) True (P.map (algebraMap A X))
  refine ⟨fun hP => d.2.2.1 fun i j h => ?_, fun hP => d.2.2.2 fun i j h => ?_⟩
  · rw [Matrix.map_apply, c.1 hP i j h, map_zero]
  · rw [Matrix.map_apply, c.2.1 hP i j h, map_zero]

private theorem mem_pairedDualFirstOrderDualMatrixSpace_of_mem_od_of_mem_ev {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}
    (T : Matrix (Fin n) (Fin n) (DD X g)) (ha : T.map DD.a = 0) (he : ∀ c, T.map (fun d => d.ep c) = 0)
    (he' : ∀ c, T.map (fun d => d.ep' c) ∈ Od A X n a) (ht : T.map DD.eta ∈ Ev A X n a) :
    T ∈ pairedDualFirstOrderDualMatrixSpace n A X g a := by
  intro i j
  have h1 := (ofPar_lemma (A := A) True (T.map DD.eta)).1 ht i j
  have h2 : ∀ c, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ False) → (T i j).ep' c = 0 := fun c =>
    (ofPar_lemma (A := A) True (T.map fun d => d.ep' c)).2.1 (he' c) i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ⟨fun _ => congrFun (congrFun ha i) j, fun _ => funext fun c => congrFun (congrFun (he c) i) j,
      fun _ => funext fun c => h2 c (by tauto), fun hf => absurd hf (by decide)⟩
  · exact ⟨fun _ => congrFun (congrFun ha i) j, fun _ => funext fun c => congrFun (congrFun (he c) i) j,
      fun hf => absurd hf (by decide), fun _ => h1 (by tauto)⟩

theorem UpperTheory.V.Pa.Det.w1sAct :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X] (Z : Matrix (Fin n) (Fin n) (DD X k.g)), Z ∈ pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a → ∀ g, k.ρ1 X g * Z * k.ρ1 X g⁻¹ ∈ pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a ∧ (∀ j, ep'M j (k.ρ1 X g * Z * k.ρ1 X g⁻¹) = x.ρX X g * ep'M j Z * x.ρX X g⁻¹) ∧ etaM (k.ρ1 X g * Z * k.ρ1 X g⁻¹) = x.ρX X g * etaM Z * x.ρX X g⁻¹ + ∑ j, ((k.κ j g).map (algebraMap x.A X) * (x.ρX X g * ep'M j Z * x.ρX X g⁻¹) - (x.ρX X g * ep'M j Z * x.ρX X g⁻¹) * (k.κ j g).map (algebraMap x.A X)) ∧ (Z * k.ρ1 X g).trace.eta = (etaM Z * x.ρX X g).trace + ∑ j, (ep'M j Z * (k.κ j g).map (algebraMap x.A X) * x.ρX X g).trace := by
  intro l _ F n x k X _ _ Z hZ g
  have hinv := (UpperTheory.V.Pa.Det.rho1Hom k X).2.2.1 g
  simp only [UpperTheory.V.Pa.Kap.ρ1] at *
  rw [hinv]
  clear hinv
  have hZ' : ∀ i j : Fin n, _ := hZ
  simp only [ddPart] at hZ'
  have hZa : Z.map DD.a = 0 := by
    ext i j
    by_cases h : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)
    · exact ((hZ' i j).1 h).1 trivial
    · exact ((hZ' i j).2 h).1 trivial
  have hZe : ∀ c : Fin k.g, Z.map (fun d => d.ep c) = 0 := by
    intro c
    ext i j
    by_cases h : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)
    · exact congrFun (((hZ' i j).1 h).2.1 trivial) c
    · exact congrFun (((hZ' i j).2 h).2.1 trivial) c
  clear hZ'
  have hR : ∀ h : F.G₀, x.ρX (DD X k.g) h = (x.ρX X h).map DD.C := by
    intro h
    funext i j
    simp only [NP.ρX, Matrix.map_apply, alg_eq]
  have hC : ∀ M : Matrix (Fin n) (Fin n) X, (M.map (DD.C (g := k.g))).map DD.a = M ∧
      (∀ c : Fin k.g, (M.map (DD.C (g := k.g))).map (fun d => d.ep c) = 0) ∧
      (∀ c : Fin k.g, (M.map (DD.C (g := k.g))).map (fun d => d.ep' c) = 0) ∧
      (M.map (DD.C (g := k.g))).map DD.eta = 0 := by
    intro M
    refine ⟨?_, fun c => ?_, fun c => ?_, ?_⟩ <;> funext i j <;> simp [DD.C_a, DD.C_ep, DD.C_ep', DD.C_eta]
  set K : Fin k.g → Matrix (Fin n) (Fin n) X := fun j => (k.κ j g).map (algebraMap x.A X) with hKdef
  have hP : ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map DD.a = 1 ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map (fun d => d.ep c) = K c) ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map (fun d => d.ep' c) = 0) ∧
      ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map DD.eta = 0 := by
    refine ⟨?_, fun c => ?_, fun c => ?_, ?_⟩ <;> funext i j <;> by_cases h : i = j <;>
      simp [Matrix.one_apply, h, DD.epM, DD.add_a, DD.add_ep, DD.add_ep', DD.add_eta, DD.one_a, DD.one_ep,
        DD.one_ep', DD.one_eta, DD.zero_a, DD.zero_ep, DD.zero_ep', DD.zero_eta]
  have hM : ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map DD.a = 1 ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map (fun d => d.ep c) = -K c) ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map (fun d => d.ep' c) = 0) ∧
      ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map DD.eta = 0 := by
    refine ⟨?_, fun c => ?_, fun c => ?_, ?_⟩ <;> funext i j <;> by_cases h : i = j <;>
      simp [sub_eq_add_neg, Matrix.one_apply, h, DD.epM, DD.add_a, DD.add_ep, DD.add_ep', DD.add_eta, DD.one_a,
        DD.one_ep, DD.one_ep', DD.one_eta, DD.zero_a, DD.zero_ep, DD.zero_ep', DD.zero_eta, DD.neg_a, DD.neg_ep,
        DD.neg_ep', DD.neg_eta]
  have htr : ∀ M : Matrix (Fin n) (Fin n) (DD X k.g), M.trace.eta = (M.map DD.eta).trace := by
    intro M
    simp only [Matrix.trace, Matrix.diag, dd_eta_sum, Matrix.map_apply]
  rw [hR g, hR g⁻¹, htr]
  obtain ⟨hCa, hCe, hCe', hCt⟩ := hC (x.ρX X g)
  obtain ⟨hCa2, hCe2, hCe'2, hCt2⟩ := hC (x.ρX X g⁻¹)
  obtain ⟨hPa, hPe, hPe', hPt⟩ := hP
  obtain ⟨hMa, hMe, hMe', hMt⟩ := hM
  refine ⟨?_, fun c => ?_, ?_, ?_⟩
  · have hρ : x.ρX X g ∈ Ev x.A X n x.a := (map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem _).1 (x.blk g)
    have hρ' : x.ρX X g⁻¹ ∈ Ev x.A X n x.a := (map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem _).1 (x.blk g⁻¹)
    have hW := (UpperTheory.V.Pa.Det.w1sMem (A := x.A) (X := X) (g := k.g) (n := n) (a := x.a)).1 Z hZ
    have hY0 : Z.map DD.eta ∈ Ev x.A X n x.a := hW.1
    have hY : ∀ c, Z.map (fun d => d.ep' c) ∈ Od x.A X n x.a := hW.2
    have hK : ∀ c, K c ∈ Od x.A X n x.a := fun c => (map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem _).2 ((k.mem c).1 g)
    apply mem_pairedDualFirstOrderDualMatrixSpace_of_mem_od_of_mem_ev
    · simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
    · intro c
      simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
    · intro c
      simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
      exact (ev_od_graded_mul_mem _ _).2.2.1 ((ev_od_graded_mul_mem _ _).2.1 hρ (hY c)) hρ'
    · simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
      exact add_mem
        ((ev_od_graded_mul_mem _ _).1 (add_mem ((ev_od_graded_mul_mem _ _).1 hρ hY0)
          (sum_mem fun c _ => (ev_od_graded_mul_mem _ _).2.2.2 ((ev_od_graded_mul_mem _ _).2.2.1 (hK c) hρ) (hY c))) hρ')
        (neg_mem (sum_mem fun c _ => (ev_od_graded_mul_mem _ _).2.2.2 ((ev_od_graded_mul_mem _ _).2.1 hρ (hY c)) ((ev_od_graded_mul_mem _ _).2.1 hρ' (hK c))))
  · simp only [ep'M, matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe,
      hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
    simp
  · simp only [etaM, ep'M, matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe,
      hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
    simp
    simp only [hKdef, Matrix.add_mul, Finset.sum_mul, Matrix.mul_assoc, Finset.sum_sub_distrib]
    abel
  · simp only [etaM, ep'M, matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe,
      hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
    simp
    simp only [hKdef, Matrix.mul_assoc]
end
end

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem clr {K : Type} [Field K] {ι : Type} [Finite ι] (y : ι → FractionRing (PowerSeries K)) :
    ∃ (s : ℕ) (a : ι → PowerSeries K), ∀ i, algebraMap _ (FractionRing (PowerSeries K)) (a i) =
      algebraMap _ (FractionRing (PowerSeries K)) ((PowerSeries.X : PowerSeries K) ^ s) * y i := by
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K)) y
  have hb0 : (b : PowerSeries K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨s, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 PowerSeries.X_irreducible
  choose r hr using hb
  refine ⟨s, fun i => ↑u⁻¹ * r i, fun i => ?_⟩
  rw [map_mul, hr i, Algebra.smul_def, hu, map_mul, ← mul_assoc, ← map_mul]
  simp

section Mp

variable {A B : Type} [CommRing A] [CommRing B] {n a : ℕ} (f : A →+* B)

private theorem mp_smul (c : A) (M : Matrix (Fin n) (Fin n) A) : f.mapMatrix (c • M) = f c • f.mapMatrix M := by
  ext i j; simp

private theorem mp_tr (M : Matrix (Fin n) (Fin n) A) : f.mapMatrix Mᵀ = (f.mapMatrix M)ᵀ := rfl

private theorem mp_trace (M : Matrix (Fin n) (Fin n) A) : (f.mapMatrix M).trace = f M.trace := by
  simp [Matrix.trace]

variable {f}

private theorem mp_inj (hf : Function.Injective f) {M N : Matrix (Fin n) (Fin n) A}
    (h : f.mapMatrix M = f.mapMatrix N) : M = N := by
  ext i j
  apply hf
  simpa using congrFun (congrFun h i) j

private theorem mp_ev (hf : Function.Injective f) {M : Matrix (Fin n) (Fin n) A} :
    f.mapMatrix M ∈ Ev B B n a ↔ M ∈ Ev A A n a := by
  simp [Ev, blkMat, map_eq_zero_iff f hf]

private theorem mp_od (hf : Function.Injective f) {M : Matrix (Fin n) (Fin n) A} :
    f.mapMatrix M ∈ Od B B n a ↔ M ∈ Od A A n a := by
  simp [Od, blkMat, map_eq_zero_iff f hf]

variable {g : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD A g)) (c : A)

private theorem eta_add : etaM (P + Q) = etaM P + etaM Q := rfl
private theorem eta_neg : etaM (-P) = -etaM P := rfl
private theorem eta_sub : etaM (P - Q) = etaM P - etaM Q := (rfl)
private theorem eta_tr : etaM Pᵀ = (etaM P)ᵀ := rfl
private theorem eta_C : etaM ((DD.C c : DD A g) • P) = c • etaM P := by
  have ha : (DD.C c : DD A g).a = c := rfl
  have he : (DD.C c : DD A g).eta = 0 := rfl
  have hp : (DD.C c : DD A g).ep = 0 := rfl
  have hq : (DD.C c : DD A g).ep' = 0 := rfl
  ext i j
  simp [etaM, ha, he, hp, hq]
private theorem eta_smul : etaM (c • P) = c • etaM P := eta_C P c
private theorem ep_add (j) : ep'M j (P + Q) = ep'M j P + ep'M j Q := rfl
private theorem ep_neg (j) : ep'M j (-P) = -ep'M j P := rfl
private theorem ep_sub (j) : ep'M j (P - Q) = ep'M j P - ep'M j Q := (rfl)
private theorem ep_tr (j) : ep'M j Pᵀ = (ep'M j P)ᵀ := rfl
private theorem ep_C (j) : ep'M j ((DD.C c : DD A g) • P) = c • ep'M j P := by
  have ha : (DD.C c : DD A g).a = c := rfl
  have hq : (DD.C c : DD A g).ep' = 0 := rfl
  ext i k
  simp [ep'M, ha, hq]
private theorem ep_smul (j) : ep'M j (c • P) = c • ep'M j P := ep_C P c j

private theorem constant_smul_mem_symmetric_deformation (h : P ∈ pairedDualFirstOrderDualMatrixSpace n A A g a) : (DD.C c : DD A g) • P ∈ pairedDualFirstOrderDualMatrixSpace n A A g a := by
  have ha : (DD.C c : DD A g).a = c := rfl
  have hp : (DD.C c : DD A g).ep = 0 := rfl
  have hq : (DD.C c : DD A g).ep' = 0 := rfl
  simp [pairedDualFirstOrderDualMatrixSpace, blkMat, ddPart] at h ⊢
  intro i j
  constructor
  · intro hij
    obtain ⟨h1, h2, h3⟩ := (h i j).1 hij
    refine ⟨by simp [h1], ?_, ?_⟩
    · funext k
      have e : (P i j).ep k = 0 := congrFun h2 k
      simp [ha, hp, h1, e]
    · funext k
      have e : (P i j).ep' k = 0 := congrFun h3 k
      simp [ha, hq, h1, e]
  · intro hij
    obtain ⟨h1, h2, h3⟩ := (h i j).2 hij
    refine ⟨by simp [h1], ?_, by simp [h3]⟩
    funext k
    have e : (P i j).ep k = 0 := congrFun h2 k
    simp [ha, hp, h1, e]

private theorem transpose_mem_symmetric_deformation (h : P ∈ pairedDualFirstOrderDualMatrixSpace n A A g a) : Pᵀ ∈ pairedDualFirstOrderDualMatrixSpace n A A g a := by
  simp [pairedDualFirstOrderDualMatrixSpace, blkMat, ddPart] at h ⊢
  intro i j
  have hji := h j i
  constructor
  · intro hij
    exact hji.1 hij.symm
  · intro hij
    exact hji.2 (fun e => hij e.symm)

end Mp

private theorem isKap {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x)
    (D : DetFr (FractionRing x.A) F.G₀ n) (ha : D.a = x.a) (hσ : D.σ = F.conj)
    (hr : ∀ g, D.r g = (algebraMap x.A (FractionRing x.A)).mapMatrix (x.ρX x.A g)) :
    D.IsKap fun j g => (algebraMap x.A (FractionRing x.A)).mapMatrix (k.κ j g) := by
  set φ := algebraMap x.A (FractionRing x.A) with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective x.A (FractionRing x.A)
  have hsel := k.mem
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j g _ h _
    have e := (hsel j).2.2.1 g h
    simp only [one_smul]
    rw [hr, hr, e, map_add, map_mul, map_mul]
  · intro j g
    rw [ha, mp_od hinj]
    exact (hsel j).1 g
  · intro j g
    rw [hσ, (hsel j).2.2.2.1 g, map_neg, mp_tr]
  · intro c Y hY hYt hc
    rw [ha] at hY
    obtain ⟨s, b, hb⟩ := clr (K := x.K) (Sum.elim c (fun p : Fin n × Fin n => Y p.1 p.2))
    set t : FractionRing x.A := φ ((PowerSeries.X : x.A) ^ s) with ht
    have ht0 : t ≠ 0 :=
      (map_ne_zero_iff φ hinj).2 (pow_ne_zero _ PowerSeries.X_ne_zero)
    let c' : Fin k.g → x.A := fun j => b (Sum.inl j)
    let Y' : Matrix (Fin n) (Fin n) x.A := fun i j => b (Sum.inr (i, j))
    have hc' : ∀ j, φ (c' j) = t * c j := fun j => hb (Sum.inl j)
    have hY' : φ.mapMatrix Y' = t • Y := by
      ext i j
      exact hb (Sum.inr (i, j))
    have hY'od : Y' ∈ Od x.A x.A n x.a := by
      rw [← mp_od hinj, hY']
      exact Submodule.smul_mem _ t hY
    have hY't : Y'ᵀ = -Y' := by
      apply mp_inj hinj
      rw [mp_tr, hY', map_neg, hY', Matrix.transpose_smul, hYt, smul_neg]
    have hfun : (∑ j, c' j • k.κ j) = dY F (x.ρX x.A) Y' := by
      funext g
      apply mp_inj hinj
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, map_sum, mp_smul, hc', mul_smul]
      rw [← Finset.smul_sum, hc g]
      simp only [dTw, dY, one_smul, map_sub, map_mul, hY', hr]
      simp [smul_sub, Matrix.mul_smul, Matrix.smul_mul]
    have hzero := k.indep c' ⟨Y', hY'od, hY't, hfun⟩
    funext j
    have e := hc' j
    rw [hzero] at e
    simp only [Pi.zero_apply, map_zero] at e
    exact (mul_eq_zero.1 e.symm).resolve_left ht0

theorem UpperTheory.V.Pa.Det.detAsm :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x), l ≠ 2 → (∃ g : F.G₀, PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → Detects k (F.G' : Set F.G₀) := by
  intro l _ F n x k hl hε
  set φ := algebraMap x.A (FractionRing x.A) with hφ
  have hinj : Function.Injective φ := IsFractionRing.injective x.A (FractionRing x.A)
  obtain ⟨D, hDa, hDG, hDr, hDσ, hDχ⟩ := UpperTheory.V.Pa.Det.detFr x hl hε
  have hr : ∀ g, D.r g = φ.mapMatrix (x.ρX x.A g) := by
    intro g
    rw [hDr]
    ext i j
    simp [NP.ρX, hφ]
  have hK := isKap k D hDa hDσ hr
  have hmapid : ∀ M : Matrix (Fin n) (Fin n) x.A, M.map (algebraMap x.A x.A) = M := by
    intro M
    ext i j
    simp
  intro z hz hell
  obtain ⟨hzW, -, hzc, hzconj⟩ := hz
  let e : F.Γ → x.A := fun g => algebraMap ℤ_[l] x.A ↑(F.ε g)
  have heps : ∀ g, epsD k x.A g = (DD.C (e g) : DD x.A k.g) := fun g => rfl
  have hχ : ∀ g : F.G₀, D.χF g = φ (e g) := hDχ
  have hW := UpperTheory.V.Pa.Det.w1sMem (A := x.A) (X := x.A) (g := k.g) (n := n) (a := x.a)
  have hact := UpperTheory.V.Pa.Det.w1sAct k x.A
  let ph : F.G₀ → Matrix (Fin n) (Fin n) (FractionRing x.A) := fun g => φ.mapMatrix (etaM (z g))
  let la : Fin k.g → F.G₀ → Matrix (Fin n) (Fin n) (FractionRing x.A) :=
    fun j g => φ.mapMatrix (ep'M j (z g))
  let s : FractionRing x.A := -φ (e F.c)
  have hee : e F.c * e F.c = 1 := by
    simp only [e, ← map_mul, ← Units.val_mul, ← map_mul F.ε, F.c_sq, map_one, Units.val_one]
  have hTw : D.IsTw (fun j g => φ.mapMatrix (k.κ j g)) s ph la := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [s, neg_mul_neg, ← map_mul, hee, map_one]
    · intro j g _ h _
      simp only [la, hzc g h, ep_add, heps, ep_C, (hact (z h) (hzW h) g).2.1 j, map_add, mp_smul,
        map_mul, hr, hχ]
    · intro j g
      rw [hDa, mp_od hinj]
      exact (hW.1 _ (hzW g)).2 j
    · intro j g
      simp only [la, hDσ, hzconj g, ep_neg, heps, ep_C, ep_tr, map_neg, mp_smul, mp_tr, s, neg_smul]
    · intro g
      rw [hDa, mp_ev hinj]
      exact (hW.1 _ (hzW g)).1
    · intro g h
      simp only [ph, la, hzc g h, eta_add, heps, eta_C, (hact (z h) (hzW h) g).2.2.1, hmapid,
        map_add, mp_smul, map_sum, map_sub, map_mul, hr, hχ]
    · intro g
      simp only [ph, hDσ, hzconj g, eta_neg, heps, eta_C, eta_tr, map_neg, mp_smul, mp_tr, s, neg_smul]
    · intro g hg
      rw [hDG] at hg
      have h0 := hell g hg
      simp only [ell, (hact (z g) (hzW g) g).2.2.2, hmapid] at h0
      simp only [ph, la, hr, ← map_mul, mp_trace, ← map_sum, ← map_add, h0, map_zero]
  obtain ⟨Y₀, Y, hY₀ev, hY₀s, hY, hph⟩ := UpperTheory.V.Pa.Det.detAlg D _ la s ph hK hTw
  obtain ⟨m, b, hb⟩ := clr (K := x.K)
    (Sum.elim (fun p : Fin n × Fin n => Y₀ p.1 p.2) (fun q : Fin k.g × Fin n × Fin n => Y q.1 q.2.1 q.2.2))
  set t : FractionRing x.A := φ ((PowerSeries.X : x.A) ^ m) with ht
  let Y₀' : Matrix (Fin n) (Fin n) x.A := fun i j => b (Sum.inl (i, j))
  let Y' : Fin k.g → Matrix (Fin n) (Fin n) x.A := fun q i j => b (Sum.inr (q, i, j))
  have hY₀' : φ.mapMatrix Y₀' = t • Y₀ := by
    ext i j
    exact hb (Sum.inl (i, j))
  have hY' : ∀ q, φ.mapMatrix (Y' q) = t • Y q := by
    intro q
    ext i j
    exact hb (Sum.inr (q, i, j))
  have hY₀'ev : Y₀' ∈ Ev x.A x.A n x.a := by
    rw [← mp_ev hinj, hY₀', ← hDa]
    exact Submodule.smul_mem _ t hY₀ev
  have hY'od : ∀ q, Y' q ∈ Od x.A x.A n x.a := by
    intro q
    rw [← mp_od hinj, hY', ← hDa]
    exact Submodule.smul_mem _ t (hY q).1
  obtain ⟨Z, hZW, hZeta, hZep⟩ := hW.2.2 Y₀' Y' hY₀'ev hY'od
  refine ⟨m, Z, hZW, ?_, ?_⟩
  · apply hW.2.1
    · rw [heps]
      exact Submodule.neg_mem _ (constant_smul_mem_symmetric_deformation _ _ (transpose_mem_symmetric_deformation _ hZW))
    · exact hZW
    · apply mp_inj hinj
      rw [heps, eta_neg, eta_C, eta_tr, hZeta, map_neg, mp_smul, mp_tr, hY₀']
      conv_rhs => rw [← hY₀s]
      simp only [s, Matrix.transpose_smul, smul_smul, neg_smul, smul_neg, mul_neg, mul_comm]
    · intro j
      apply mp_inj hinj
      rw [heps, ep_neg, ep_C, ep_tr, hZep, map_neg, mp_smul, mp_tr, hY']
      conv_rhs => rw [← (hY j).2.1]
      simp only [s, Matrix.transpose_smul, smul_smul, neg_smul, smul_neg, mul_neg, mul_comm]
  · funext g
    apply hW.2.1
    · exact Submodule.smul_mem _ _ (hzW g)
    · rw [heps]
      exact Submodule.sub_mem _ (constant_smul_mem_symmetric_deformation _ _ (hact Z hZW g).1) hZW
    · apply mp_inj hinj
      have h1 := hph g
      simp only [ph] at h1
      simp only [Pi.smul_apply, eta_smul, heps, eta_sub, eta_C, (hact Z hZW g).2.2.1, hmapid,
        hZeta, hZep, map_sub, map_add, mp_smul, map_sum, map_mul, ← hr, hY₀', hY', h1, dTw, hχ]
      simp only [smul_add, smul_sub, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
        mul_comm]
      abel
    · intro j
      apply mp_inj hinj
      have h1 := (hY j).2.2 g
      simp only [la] at h1
      simp only [Pi.smul_apply, ep_smul, heps, ep_sub, ep_C, (hact Z hZW g).2.1 j,
        hZep, map_sub, mp_smul, map_mul, ← hr, hY', h1, dTw, hχ]
      simp only [smul_sub, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]
      rfl
end
