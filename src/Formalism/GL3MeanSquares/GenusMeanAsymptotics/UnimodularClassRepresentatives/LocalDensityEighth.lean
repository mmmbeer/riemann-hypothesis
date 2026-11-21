import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardQuotExtPPow

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences

open idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem exists_trace_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (N : ℕ) : ∃ a : 𝓞 K, a + star a - 1 ∈ extP K 𝔭 ^ N := by
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := exists_inv_theta hθ N
  refine ⟨θ * e, ?_⟩
  have hJ := conjO_mem_pow hF 𝔭 N
  have h1 : (conjO K θ - θ) * conjO K e - 1 ∈ extP K 𝔭 ^ N := by
    have h := hJ _ he
    simp only [map_sub, map_mul, map_one] at h
    rw [L3.conjO_conjO θ] at h
    exact h
  have h2 : (θ - conjO K θ) * (e + conjO K e) ∈ extP K 𝔭 ^ N := by
    have e2 : (θ - conjO K θ) * (e + conjO K e) =
        ((θ - conjO K θ) * e - 1) - ((conjO K θ - θ) * conjO K e - 1) := by ring
    rw [e2]
    exact Ideal.sub_mem _ he h1
  have h3 : e + conjO K e ∈ extP K 𝔭 ^ N := mem_of_unit_mul_mem hθ h2
  have e3 : θ * e + star (θ * e) - 1 =
      ((θ - conjO K θ) * e - 1) + conjO K θ * (e + conjO K e) := by
    rw [idealPowerSpanBounds.star_def, map_mul]
    ring
  rw [e3]
  exact Ideal.add_mem _ he (Ideal.mul_mem_left _ _ h3)

theorem exists_tr_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {N : ℕ} {z : 𝓞 K} (hz : z ∉ extP K 𝔭 ^ N) :
    ∃ b : 𝓞 K, trF hF (b * z) ∉ 𝔭 ^ N := by
  by_contra hall
  push_neg at hall
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  have htr : ∀ b : 𝓞 K, b * z + conjO K (b * z) ∈ extP K 𝔭 ^ N := by
    intro b
    rw [← trF_spec hF]
    exact (mem_pow_iff 𝔭 N _).mpr (hall b)
  have h1 := htr 1
  have h2 := htr θ
  rw [one_mul] at h1
  rw [map_mul] at h2
  have h3 : (θ - conjO K θ) * conjO K z ∈ extP K 𝔭 ^ N := by
    have e : (θ - conjO K θ) * conjO K z =
        θ * (z + conjO K z) - (θ * z + conjO K θ * conjO K z) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) h2
  have h4 : conjO K z ∈ extP K 𝔭 ^ N := mem_of_unit_mul_mem hθ h3
  apply hz
  have h5 := conjO_mem_pow hF 𝔭 N _ h4
  rwa [L3.conjO_conjO z] at h5

theorem exists_solve_scalar (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c k : ℕ} (hck : c ≤ k) {z₀ : 𝓞 K} (hz : z₀ ∉ extP K 𝔭 ^ (c + 1)) {s : 𝓞 K}
    (hs : s ∈ extP K 𝔭 ^ k) (hs' : star s - s ∈ extP K 𝔭 ^ (k + 1)) :
    ∃ r ∈ extP K 𝔭 ^ (k - c), z₀ * r + star (z₀ * r) - s ∈ extP K 𝔭 ^ (k + 1) := by
  obtain ⟨a, ha⟩ := exists_trace_one hK hF h𝔭 (k + 1)
  have has : a * s ∈ extP K 𝔭 ^ k := Ideal.mul_mem_left _ a hs
  have hσ : trF hF (a * s) ∈ 𝔭 ^ k := trF_mem_pow hF 𝔭 k has
  have hσs : ι (trF hF (a * s)) - s ∈ extP K 𝔭 ^ (k + 1) := by
    rw [trF_spec, map_mul]
    have e : a * s + conjO K a * conjO K s - s =
        (a + star a - 1) * s + conjO K a * (star s - s) := by
      rw [idealPowerSpanBounds.star_def, idealPowerSpanBounds.star_def]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hs')
  obtain ⟨b, hb⟩ := exists_tr_notMem hK hF h𝔭 hz
  obtain ⟨r', hr', hfill⟩ := idealPowerSpanBounds.exists_fill h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) hb hck hσ
  refine ⟨b * ι r', Ideal.mul_mem_left _ b ((mem_pow_iff 𝔭 (k - c) r').mpr hr'), ?_⟩
  have hlin : trF hF (z₀ * (b * ι r')) = r' * trF hF (b * z₀) := by
    have e : z₀ * (b * ι r') = r' • (b * z₀) := by
      rw [Algebra.smul_def]
      ring
    rw [e, map_smul, smul_eq_mul]
  have hsum : z₀ * (b * ι r') + star (z₀ * (b * ι r')) = ι (r' * trF hF (b * z₀)) := by
    rw [← hlin, trF_spec, idealPowerSpanBounds.star_def]
  rw [hsum]
  have e2 : ι (r' * trF hF (b * z₀)) - s =
      -ι (trF hF (a * s) - trF hF (b * z₀) * r') + (ι (trF hF (a * s)) - s) := by
    simp only [map_sub, map_mul]
    ring
  rw [e2]
  exact Ideal.add_mem _ (neg_mem ((mem_pow_iff 𝔭 (k + 1) _).mpr hfill)) hσs

variable {m : Type} [Fintype m] [DecidableEq m]

theorem mul_entries_mem {r : Type} {J : Ideal (𝓞 K)} (M : Matrix m m (𝓞 K)) {R : Matrix m r (𝓞 K)}
    (hR : ∀ i j, R i j ∈ J) (i : m) (j : r) : (M * R) i j ∈ J := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_left _ _ (hR l j))

theorem exists_solve_matrix (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c k : ℕ} (hck : c + 1 ≤ k) {H X : Matrix m m (𝓞 K)} {D : 𝓞 F}
    (hD : H.det = ι D) (hDc : D ∉ 𝔭 ^ (c + 1)) (hX : ∀ i j, (Xᴴ * H * X - H) i j ∈ extP K 𝔭 ^ k)
    {W : Matrix m m (𝓞 K)} (hW : ∀ i j, W i j ∈ extP K 𝔭 ^ k) :
    ∃ Y : Matrix m m (𝓞 K), (∀ i j, Y i j ∈ extP K 𝔭 ^ (k - c)) ∧
      ∀ i j, (Xᴴ * H * Y - W) i j ∈ extP K 𝔭 ^ (k + 1) := by
  have hck' : c ≤ k := by omega
  have hfill := fun i j => exists_fillO (K := K) h𝔭 hDc hck' (hW i j)
  choose V hV hV' using hfill
  obtain ⟨R, hR⟩ : ∃ R : Matrix m m (𝓞 K), R = H.adjugate * Matrix.of V := ⟨_, rfl⟩
  have hRmem : ∀ i j, R i j ∈ extP K 𝔭 ^ (k - c) := by
    intro i j
    rw [hR]
    exact mul_entries_mem _ (fun a b => hV a b) i j
  refine ⟨X * R, fun i j => mul_entries_mem X hRmem i j, ?_⟩
  intro i j
  have e : Xᴴ * H * (X * R) - W = (Xᴴ * H * X - H) * R + (H * R - W) := by
    first
    | noncomm_ring
    | (simp only [Matrix.sub_mul, Matrix.mul_assoc]; abel)
  have e1 : H * R = H.det • Matrix.of V := by
    rw [hR, ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
  rw [e, Matrix.add_apply]
  refine Ideal.add_mem _ ?_ ?_
  · rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ (fun l _ => ?_)
    have h1 : (Xᴴ * H * X - H) i l * R l j ∈ extP K 𝔭 ^ (k + (k - c)) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul (hX i l) (hRmem l j)
    exact Ideal.pow_le_pow_right (by omega) h1
  · rw [Matrix.sub_apply, e1, Matrix.smul_apply, Matrix.of_apply, hD, smul_eq_mul]
    have h2 := neg_mem (hV' i j)
    rw [neg_sub] at h2
    exact h2

end Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
end
end

section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms

open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m r : Type} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

abbrev mkk (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    𝓞 K →+* 𝓞 K ⧸ extP K 𝔭 ^ k := Ideal.Quotient.mk (extP K 𝔭 ^ k)

theorem exists_lift {a b : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : Matrix a b (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    ∃ Y : Matrix a b (𝓞 K), Y.map (mkk K 𝔭 k) = X := by
  choose f hf using fun x : 𝓞 K ⧸ extP K 𝔭 ^ k => Ideal.Quotient.mk_surjective x
  refine ⟨X.map f, ?_⟩
  ext i j
  simp [hf]

theorem map_conjTranspose {a b : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : Matrix a b (𝓞 K)) :
    (X.map (mkk K 𝔭 k))ᴴ = Xᴴ.map (mkk K 𝔭 k) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  exact idealPowerSpanBounds.star_mk 𝔭 k (X j i)

theorem map_form {a b : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H : Matrix m m (𝓞 K)) (X : Matrix m a (𝓞 K))
    (Y : Matrix m b (𝓞 K)) :
    (X.map (mkk K 𝔭 k))ᴴ * H.map (mkk K 𝔭 k) * Y.map (mkk K 𝔭 k) = (Xᴴ * H * Y).map (mkk K 𝔭 k) := by
  rw [map_conjTranspose, Matrix.map_mul, Matrix.map_mul]

theorem map_map_piQ {a b : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : Matrix a b (𝓞 K)) :
    (X.map (mkk K 𝔭 (k + 1))).map (piQ K 𝔭 k) = X.map (mkk K 𝔭 k) := rfl

theorem absNorm_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 0 < Ideal.absNorm 𝔭 := Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact idealPowerSpanBounds.ne_bot h𝔭)

theorem exists_unit_quot (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    ∃ θ e : 𝓞 K ⧸ extP K 𝔭 ^ k, (θ - star θ) * e = 1 := by
  obtain ⟨θ, hθ⟩ := exists_theta hK (Fact.out : IsFixF K F) h𝔭
  obtain ⟨e, he⟩ := exists_inv_theta hθ k
  refine ⟨Ideal.Quotient.mk _ θ, Ideal.Quotient.mk _ e, ?_⟩
  rw [idealPowerSpanBounds.star_mk, idealPowerSpanBounds.star_def, ← map_sub, ← map_mul,
    ← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]
  exact he

theorem card_hermSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (hermSub r (RingHom.ker (piQ K 𝔭 k))) =
      Ideal.absNorm 𝔭 ^ (Fintype.card r * Fintype.card r) := by
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  have hF : IsFixF K F := Fact.out
  obtain ⟨θ, e, he⟩ := exists_unit_quot hK h𝔭 (k + 1)
  have hJ : ∀ a ∈ RingHom.ker (piQ K 𝔭 k), star a ∈ RingHom.ker (piQ K 𝔭 k) := by
    intro a ha
    rw [ker_piQ] at ha ⊢
    exact star_mem_idQ ha
  have h1 := card_hermSub_sq (r := r) hJ he
  rw [card_entSub, card_ker_piQ hK hF h𝔭 k, ← pow_mul, mul_comm 2, pow_mul] at h1
  exact Nat.pow_left_injective (by norm_num) h1

theorem card_rep_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (H : Matrix m m (𝓞 K)) (hH : Hᴴ = H) (T : Matrix r r (𝓞 K)) (hT : Tᴴ = T) {k j : ℕ}
    (hj : k + 1 ≤ 2 * j) (p' : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ k) → Prop)
    (hinv : ∀ X Y : Matrix m r (𝓞 K), (∀ a b, Y a b ∈ extP K 𝔭 ^ j) →
      (p' ((X + Y).map (mkk K 𝔭 k)) ↔ p' (X.map (mkk K 𝔭 k))))
    (RC : ∀ X : Matrix m r (𝓞 K), p' (X.map (mkk K 𝔭 k)) →
      (∀ a b, (Xᴴ * H * X - T) a b ∈ extP K 𝔭 ^ k) → ∀ S : Matrix r r (𝓞 K),
      (∀ a b, S a b ∈ extP K 𝔭 ^ k) → (∀ a b, (Sᴴ - S) a b ∈ extP K 𝔭 ^ (k + 1)) →
      ∃ Y : Matrix m r (𝓞 K), (∀ a b, Y a b ∈ extP K 𝔭 ^ j) ∧
        ∀ a b, (Xᴴ * H * Y + Yᴴ * H * X - S) a b ∈ extP K 𝔭 ^ (k + 1)) :
    Nat.card {X : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) // p' (X.map (piQ K 𝔭 k)) ∧
        Xᴴ * H.map (mkk K 𝔭 (k + 1)) * X = T.map (mkk K 𝔭 (k + 1))} *
        Ideal.absNorm 𝔭 ^ (Fintype.card r * Fintype.card r) =
      Ideal.absNorm 𝔭 ^ (2 * (Fintype.card m * Fintype.card r)) *
        Nat.card {X : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ k) // p' X ∧
          Xᴴ * H.map (mkk K 𝔭 k) * X = T.map (mkk K 𝔭 k)} := by
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  have hF : IsFixF K F := Fact.out
  have hHq : (H.map (mkk K 𝔭 (k + 1)))ᴴ = H.map (mkk K 𝔭 (k + 1)) := by
    rw [map_conjTranspose, hH]
  have hTq : (T.map (mkk K 𝔭 (k + 1)))ᴴ = T.map (mkk K 𝔭 (k + 1)) := by
    rw [map_conjTranspose, hT]
  have hinv' : ∀ X Y : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)),
      Y ∈ entSub m r (idQ K 𝔭 (k + 1) j) →
      (p' ((X + Y).map (piQ K 𝔭 k)) ↔ p' (X.map (piQ K 𝔭 k))) := by
    intro X Y hY
    obtain ⟨X0, rfl⟩ := exists_lift 𝔭 (k + 1) X
    have hY1 : ∀ a b, Y a b ∈ idQ K 𝔭 (k + 1) j := hY
    have hY' : ∀ a b, ∃ z ∈ extP K 𝔭 ^ j, Ideal.Quotient.mk _ z = Y a b :=
      fun a b => mem_idQ.mp (hY1 a b)
    choose Y0 hY0 hY0' using hY'
    have hsum : X0.map (mkk K 𝔭 (k + 1)) + Y = (X0 + Matrix.of Y0).map (mkk K 𝔭 (k + 1)) := by
      ext a b
      simp only [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, map_add, hY0']
    rw [hsum, map_map_piQ, map_map_piQ]
    exact hinv X0 (Matrix.of Y0) hY0
  have RC' : ∀ X : Matrix m r (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)), p' (X.map (piQ K 𝔭 k)) →
      (∀ i j, (Xᴴ * H.map (mkk K 𝔭 (k + 1)) * X - T.map (mkk K 𝔭 (k + 1))) i j ∈
        RingHom.ker (piQ K 𝔭 k)) →
      ∀ S ∈ hermSub r (RingHom.ker (piQ K 𝔭 k)), ∃ Y ∈ entSub m r (idQ K 𝔭 (k + 1) j),
        Xᴴ * H.map (mkk K 𝔭 (k + 1)) * Y + Yᴴ * H.map (mkk K 𝔭 (k + 1)) * X = S := by
    intro X hpX hX S hS
    obtain ⟨X0, rfl⟩ := exists_lift 𝔭 (k + 1) X
    rw [map_map_piQ] at hpX
    have hX0 : ∀ a b, (X0ᴴ * H * X0 - T) a b ∈ extP K 𝔭 ^ k := by
      intro a b
      have h1 := hX a b
      rw [map_form, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub,
        ← Matrix.sub_apply] at h1
      exact (mk_mem_ker_piQ 𝔭 k _).mp h1
    have hS1 := HermitianSublattices.mem_hermSub.mp hS
    have hSe : ∀ a b, ∃ z ∈ extP K 𝔭 ^ k, Ideal.Quotient.mk _ z = S a b := by
      intro a b
      have h2 := hS1.2 a b
      rw [ker_piQ] at h2
      exact mem_idQ.mp h2
    choose S0 hS0 hS0' using hSe
    have hSmap : S = (Matrix.of S0).map (mkk K 𝔭 (k + 1)) := by
      ext a b
      exact (hS0' a b).symm
    have hS0h : ∀ a b, ((Matrix.of S0)ᴴ - Matrix.of S0) a b ∈ extP K 𝔭 ^ (k + 1) := by
      intro a b
      have h3 := congrFun (congrFun hS1.1 a) b
      rw [hSmap, map_conjTranspose] at h3
      simp only [Matrix.map_apply] at h3
      rw [Matrix.sub_apply]
      exact Ideal.Quotient.eq.mp h3
    obtain ⟨Y0, hY0, hY0'⟩ := RC X0 hpX hX0 (Matrix.of S0) (fun a b => hS0 a b) hS0h
    refine ⟨Y0.map (mkk K 𝔭 (k + 1)), fun a b => mem_idQ.mpr ⟨Y0 a b, hY0 a b, rfl⟩, ?_⟩
    rw [hSmap, map_form, map_form]
    ext a b
    simp only [Matrix.add_apply, Matrix.map_apply]
    rw [← map_add, Ideal.Quotient.eq]
    have h4 := hY0' a b
    simpa only [Matrix.sub_apply, Matrix.add_apply] using h4
  have h := card_lift_matrix (piQ K 𝔭 k) (piQ_surjective 𝔭 k) (piQ_star 𝔭 k)
    (idQ K 𝔭 (k + 1) j) (fun a ha => star_mem_idQ ha) (fun a ha b hb => mul_eq_zero_idQ hj ha hb)
    (H.map (mkk K 𝔭 (k + 1))) hHq (T.map (mkk K 𝔭 (k + 1))) hTq p' hinv' RC'
  rw [card_hermSub hK h𝔭 k, card_entSub, card_ker_piQ hK hF h𝔭 k, map_map_piQ, map_map_piQ,
    ← pow_mul] at h
  exact h

end Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
end
end
