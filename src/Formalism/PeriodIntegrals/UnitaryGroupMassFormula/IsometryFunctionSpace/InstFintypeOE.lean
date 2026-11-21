import Mathlib
import Formalism.PeriodIntegrals.IsoFunV

section
open Matrix Finset Equiv

namespace PI.IsoFunVW

theorem finite_oe (m n : ℕ) : Finite (Fin m ↪o Fin n) :=
  Finite.of_injective (fun e : Fin m ↪o Fin n => (e : Fin m → Fin n))
    (fun _ _ h => RelEmbedding.ext (congrFun h))

theorem det_mul_eq_sum_fun {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ f : Fin m → Fin n, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  have hdet : (A * B).det = (detRowAlternating : (Fin m → R) [⋀^Fin m]→ₗ[R] R)
      (fun (i : Fin m) => ∑ b : Fin n, A i b • (B b : Fin m → R)) := by
    rw [Matrix.det]; congr 1; ext i j; simp [Matrix.mul_apply, Finset.sum_apply]
  have hs := (detRowAlternating : (Fin m → R) [⋀^Fin m]→ₗ[R] R).toMultilinearMap.map_sum
    (fun (i : Fin m) (b : Fin n) => A i b • (B b : Fin m → R))
  rw [hdet]
  refine hs.trans (Finset.sum_congr rfl (fun f _ => ?_))
  have := (detRowAlternating : (Fin m → R) [⋀^Fin m]→ₗ[R] R).toMultilinearMap.map_smul_univ
    (fun i => A i (f i)) (fun i => (B (f i) : Fin m → R))
  refine this.trans ?_
  rw [smul_eq_mul]
  rfl

theorem det_submatrix_noninj {R : Type*} [CommRing R] {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) R) (f : Fin m → Fin n) (hf : ¬ Function.Injective f) :
    (B.submatrix f id).det = 0 := by
  simp only [Function.Injective, not_forall] at hf
  obtain ⟨i, j, hij, hne⟩ := hf
  exact det_zero_of_row_eq hne (by ext k; simp [hij])

theorem det_mul_eq_sum_oe {R : Type*} [CommRing R] {m n : ℕ} [Fintype (Fin m ↪o Fin n)]
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ J : Fin m ↪o Fin n, (A.submatrix id J).det * (B.submatrix J id).det := by
  classical
  rw [det_mul_eq_sum_fun]
  set g : (Fin m → Fin n) → R := fun f => (∏ i, A i (f i)) * (B.submatrix f id).det with hg
  have h1 : ∑ f : Fin m → Fin n, g f =
      ∑ f ∈ univ.filter (fun f : Fin m → Fin n => Function.Injective f), g f := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    split_ifs with hf
    · rfl
    · simp [hg, det_submatrix_noninj B f hf]
  have h2 : ∀ J : Fin m ↪o Fin n, (A.submatrix id J).det * (B.submatrix J id).det
      = ∑ σ : Perm (Fin m), g (fun i => J (σ i)) := by
    intro J
    rw [← det_transpose (A.submatrix id J), det_apply', Finset.sum_mul]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    have hB : (B.submatrix (fun i => J (σ i)) id) = (B.submatrix J id).submatrix σ id := by
      ext i j; rfl
    simp only [hg, hB, det_permute]
    simp only [transpose_apply, submatrix_apply, id]
    ring
  rw [h1]
  simp_rw [h2]
  rw [← Fintype.sum_prod_type' (fun (J : Fin m ↪o Fin n) (σ : Perm (Fin m)) => g (fun i => J (σ i)))]
  symm
  refine Finset.sum_bij (fun p _ => fun i => p.1 (p.2 i)) ?_ ?_ ?_ ?_
  · intro p _
    simp only [mem_filter, mem_univ, true_and]
    exact p.1.injective.comp p.2.injective
  · intro p _ q _ h
    have hr : Set.range (p.1 : Fin m → Fin n) = Set.range (q.1 : Fin m → Fin n) := by
      have e1 : Set.range (fun i => p.1 (p.2 i)) = Set.range (p.1 : Fin m → Fin n) :=
        p.2.surjective.range_comp _
      have e2 : Set.range (fun i => q.1 (q.2 i)) = Set.range (q.1 : Fin m → Fin n) :=
        q.2.surjective.range_comp _
      rw [← e1, ← e2, h]
    have hJ : p.1 = q.1 :=
      RelEmbedding.ext (congrFun ((p.1.strictMono.range_inj q.1.strictMono).1 hr))
    have hσ : p.2 = q.2 := by
      ext i
      have := congrFun h i
      rw [hJ] at this
      exact congrArg Fin.val (q.1.injective this)
    exact Prod.ext hJ hσ
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    have hs : (univ.image f).card = m := by
      rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin]
    set J := (univ.image f).orderEmbOfFin hs
    have hmem : ∀ i, ∃ k, J k = f i := by
      intro i
      have : f i ∈ Set.range J := by
        rw [Finset.range_orderEmbOfFin]; simp
      exact this
    choose τ hτ using hmem
    have hτi : Function.Injective τ := by
      intro a b hab
      apply hf
      rw [← hτ a, ← hτ b, hab]
    refine ⟨(J, Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτi)), mem_univ _, ?_⟩
    funext i
    simp [hτ]
  · intro p _
    rfl

end PI.IsoFunVW
end

section
open Matrix Finset MvPolynomial

noncomputable section

namespace PI.IsoFunVW

open PI.IsoFunV

noncomputable instance instFintypeOE (m n : ℕ) : Fintype (Fin m ↪o Fin n) :=
  @Fintype.ofFinite _ (finite_oe m n)

noncomputable instance instFintypeCC {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) : Fintype (ColChoice N nu) := by
  unfold ColChoice; infer_instance

def linW {σ : Type} (w : (σ →₀ ℕ) → ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun P := ∑ α ∈ P.support, coeff α P * w α
  map_add' P Q := by
    classical
    have key : ∀ (R : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)), R.support ⊆ S →
        ∑ α ∈ R.support, coeff α R * w α = ∑ α ∈ S, coeff α R * w α := by
      intro R S hS
      refine Finset.sum_subset hS (fun α _ hα => ?_)
      rw [MvPolynomial.mem_support_iff, not_not] at hα
      simp [hα]
    rw [key (P + Q) (P.support ∪ Q.support) support_add,
      key P (P.support ∪ Q.support) subset_union_left,
      key Q (P.support ∪ Q.support) subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [coeff_add, add_mul]
  map_smul' c P := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine (Finset.sum_subset support_smul (fun α _ hα => ?_)).trans ?_
    · rw [MvPolynomial.mem_support_iff, not_not] at hα
      simp [hα]
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [coeff_smul, smul_eq_mul, mul_assoc]

theorem linW_apply {σ : Type} (w : (σ →₀ ℕ) → ℂ) (P : MvPolynomial σ ℂ) :
    linW w P = ∑ α ∈ P.support, coeff α P * w α := rfl

def wTh {T : Type} [Fintype T] {N N' : ℕ} (Θ : VC T N N' → ℂ) (α : Mono T N N') : ℂ :=
  (α.prod fun _ n => (n.factorial : ℂ)) * taylor Θ α

theorem applyAt0_eq {T : Type} [Fintype T] {N N' : ℕ} (P : MvPolynomial (Idx T N N') ℂ)
    (Θ : VC T N N' → ℂ) : applyAt0 P Θ = linW (wTh Θ) P := by
  rw [linW_apply, applyAt0]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [wTh, mul_assoc]

theorem minY_map {Lt k k' : Type} [Fintype Lt] [CommRing k] [CommRing k'] (f : k →+* k')
    (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu) (y : Lt → Fin N → ℕ → k) :
    f (minY N nu J y) = minY N nu J (fun z a j => f (y z a j)) := by
  simp only [minY, map_prod, RingHom.map_det]
  rfl

def yfr {Lt T : Type} (tp : Lt → T) {N N' : ℕ} (s : T → ℂ) (x : Lt → Fin N → ℕ → ℂ) :
    Lt → Fin N' → ℕ → MvPolynomial (Idx T N N') ℂ :=
  fun z a j => ∑ b : Fin N, C (s (tp z)) * X ((tp z, a, b) : Idx T N N') * C (x z b j)

theorem prod_sum_cc {Lt : Type} [Fintype Lt] [DecidableEq Lt] {R : Type} [CommRing R] (N : ℕ)
    (nu : Lt → YoungDiagram)
    (F : ∀ (z : Lt) (c : Fin ((nu z).rowLen 0)), (Fin ((nu z).colLen c) ↪o Fin N) → R) :
    ∏ z, ∏ c, ∑ Jc, F z c Jc = ∑ J : ColChoice N nu, ∏ z, ∏ c, F z c (J z c) := by
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)

theorem key_id {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (x : Lt → Fin N → ℕ → ℂ) (I : ColChoice N' nu) :
    ∑ J : ColChoice N nu, PIJ tp nu s I J * C (minY N nu J x) = minY N' nu I (yfr tp s x) := by
  have hR : ∀ J : ColChoice N nu, PIJ tp nu s I J * C (minY N nu J x) =
      ∏ z, ∏ c : Fin ((nu z).rowLen 0),
        (Matrix.of fun i k : Fin ((nu z).colLen c) =>
          C (s (tp z)) * X ((tp z, I z c i, J z c k) : Idx T N N')).det *
        (Matrix.of fun i j : Fin ((nu z).colLen c) =>
          (C (x z (J z c i) (j : ℕ)) : MvPolynomial (Idx T N N') ℂ)).det := by
    intro J
    rw [minY_map]
    simp only [PIJ, minY, ← Finset.prod_mul_distrib]
  have hL : minY N' nu I (yfr tp s x) = ∏ z, ∏ c : Fin ((nu z).rowLen 0),
      ∑ Jc : Fin ((nu z).colLen c) ↪o Fin N,
        (Matrix.of fun i k : Fin ((nu z).colLen c) =>
          C (s (tp z)) * X ((tp z, I z c i, Jc k) : Idx T N N')).det *
        (Matrix.of fun i j : Fin ((nu z).colLen c) =>
          (C (x z (Jc i) (j : ℕ)) : MvPolynomial (Idx T N N') ℂ)).det := by
    simp only [minY]
    refine Finset.prod_congr rfl (fun z _ => Finset.prod_congr rfl (fun c _ => ?_))
    have hcb := det_mul_eq_sum_oe
      (Matrix.of fun (i : Fin ((nu z).colLen c)) (b : Fin N) =>
        C (s (tp z)) * X ((tp z, I z c i, b) : Idx T N N'))
      (Matrix.of fun (b : Fin N) (j : Fin ((nu z).colLen c)) =>
        (C (x z b (j : ℕ)) : MvPolynomial (Idx T N N') ℂ))
    have hm : (Matrix.of fun i j : Fin ((nu z).colLen c) => yfr tp s x z (I z c i) (j : ℕ)) =
        (Matrix.of fun (i : Fin ((nu z).colLen c)) (b : Fin N) =>
          C (s (tp z)) * X ((tp z, I z c i, b) : Idx T N N')) *
        (Matrix.of fun (b : Fin N) (j : Fin ((nu z).colLen c)) =>
          (C (x z b (j : ℕ)) : MvPolynomial (Idx T N N') ℂ)) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.of_apply, yfr]
    rw [hm, hcb]
    rfl
  rw [hL, prod_sum_cc]
  exact Finset.sum_congr rfl (fun J _ => hR J)

theorem AOp_eq {Lt T : Type} [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ) (φ : LaC N nu) (I : ColChoice N' nu) :
    AOp tp nu s Θ φ I = ∑ J : ColChoice N nu, applyAt0 (PIJ tp nu s I J) Θ * φ J := by
  rw [AOp, finsum_eq_sum_of_fintype]

theorem AOp_hv {Lt T : Type} [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ) (x : Lt → Fin N → ℕ → ℂ) :
    AOp tp nu s Θ (hvC N nu x) = fun I => linW (wTh Θ) (minY N' nu I (yfr tp s x)) := by
  funext I
  rw [AOp_eq, ← key_id, map_sum]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [applyAt0_eq, mul_comm (PIJ tp nu s I J), ← MvPolynomial.smul_eq_C_mul, map_smul,
    smul_eq_mul, mul_comm]
  rfl

def AOpLin {Lt T : Type} [Fintype Lt] [DecidableEq Lt] [Fintype T] (tp : Lt → T) {N N' : ℕ}
    (nu : Lt → YoungDiagram) (s : T → ℂ) (Θ : VC T N N' → ℂ) : LaC N nu →ₗ[ℂ] LaC N' nu where
  toFun φ := AOp tp nu s Θ φ
  map_add' φ ψ := by
    funext I
    simp only [AOp_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    funext I
    simp only [AOp_eq, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun J _ => ?_)
    ring

end PI.IsoFunVW

end
end
