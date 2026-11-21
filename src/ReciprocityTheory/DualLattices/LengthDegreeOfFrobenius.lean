import ReciprocityTheory.DualLattices.InvolutionPermApplyZero
import ReciprocityTheory.DualLattices.EigenQuotientSmithStatement
import ReciprocityTheory.DualLattices.PowMemCarrier
import ReciprocityTheory.DualLattices.SumValCoord
import ReciprocityTheory.DualLattices.VDetEqOneOfIntegral
import ReciprocityTheory.DualLattices.RestrictedHopfOrderApproximationStatement
import ReciprocityTheory.DualLattices.MemAugIdeal
import ReciprocityTheory.DualLattices.ExistsMatOfEquiv
import ReciprocityTheory.DualLattices.BasechangeProjectorIdempotentAction
import ReciprocityTheory.DualLattices.StdJForm4
import ReciprocityTheory.DualLattices.KilledGen
import ReciprocityTheory.DualLattices.IdemGen
import ReciprocityTheory.DualLattices.LenEx
import ReciprocityTheory.DualLattices.CokernelLengthComparisonOf

section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

lemma idem_basis {S : Type} [CommRing S] [IsLocalRing S] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι S) (hP : P * P = P) : ∃ (r : ℕ) (Bw : Matrix ι (Fin r) S),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin P) ∧
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ := by
  classical
  let f : (ι → S) →ₗ[S] (ι → S) := Matrix.mulVecLin P
  have hidem : ∀ x, f (f x) = f x := fun x => by
    simp only [f, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]
  let M := LinearMap.range f
  have hsplit : f.rangeRestrict ∘ₗ M.subtype = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨y, x, rfl⟩
    apply Subtype.ext
    simp [hidem]
  haveI : Module.Projective S M := Module.Projective.of_split M.subtype f.rangeRestrict hsplit
  haveI : Module.Free S M := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis S M
  have hBw : Matrix.mulVecLin (Matrix.of fun i j => (b j : ι → S) i) =
      M.subtype ∘ₗ b.equivFun.symm.toLinearMap := by
    apply LinearMap.ext
    intro c
    funext i
    simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, Finset.sum_apply, mul_comm]
  refine ⟨Module.finrank S M, Matrix.of fun i j => (b j : ι → S) i, ?_, ?_⟩
  · rw [hBw, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), Submodule.range_subtype]
  · rw [hBw, LinearMap.ker_eq_bot]
    exact M.injective_subtype.comp b.equivFun.symm.injective

theorem wdetDegree_of_smith_restrict (hS : EigenQuotientSmithStatement) (hR : RestrictedHopfOrderStatement) (hC : RestrictedHopfOrderApproximationStatement) :
    WdetDegStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw d X hd hX
  classical
  have hv := hSet.integers
  have hidem : e w * e w = e w := by rw [horth, if_pos rfl]
  have hρidem : H.ρ (e w) * H.ρ (e w) = H.ρ (e w) := by rw [← map_mul, hidem]
  obtain ⟨r, Bw, hrange, hker⟩ := idem_basis (H.ρ (e w)) hρidem
  obtain ⟨Λ, dj, hΛ, hdjspan, hdjv, hXeq⟩ :=
    hS p g C v R O σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange hker X hX
  obtain ⟨AW, hAWc, hOm⟩ := hR p g C v R O σ cp hSet H (e w) hidem r Bw hrange hker d hd
  have hcl := fun j => hC p g C v R O σ cp hSet H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange
    hker (Λ j) (dj j) (hdjspan j) (hdjv j)
  choose x hxmem hxapp using hcl
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcp0 : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h1 := hSet.cp_val
    rw [h0, zero_pow (by omega)] at h1
    exact hSet.p_ne h1.symm
  have hdj0 : ∀ j, algebraMap R C (dj j) ≠ 0 := fun j h0 => by
    have h1 := hdjv j
    rw [h0, map_zero, le_zero_iff] at h1
    exact hcp0 h1
  have hpC : v (p : C) < 1 := by
    have h1 := hSet.p_lt
    rwa [map_natCast] at h1
  set u : Fin r → (Fin r → ZMod p) → C := fun j y => (algebraMap R C (dj j))⁻¹ * x j y with hudef
  have hred : ∀ y : Fin r → ZMod p, (fun i => PadicInt.toZMod (((y i).val : ℕ) : ℤ_[p])) = y := by
    intro y
    funext i
    simp
  have hU2 : ∀ j y, v (u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R))) < 1 := by
    intro j y
    have h1 := hxapp j (fun i => (((y i).val : ℕ) : ℤ_[p]))
    rw [hred y] at h1
    simp only [map_natCast] at h1
    have e1 : u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R)) =
        (x j y - algebraMap R C (dj j * ∑ i, Λ j i * ((y i).val : R))) / algebraMap R C (dj j) := by
      simp only [hudef, map_mul]
      field_simp [hdj0 j]
    rw [e1, map_div₀]
    exact (div_lt_one (pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 (hdj0 j)))).2 h1
  have hU1 : ∀ j y, v (u j y) ≤ 1 := by
    intro j y
    have e1 : u j y = (u j y - algebraMap R C (∑ i, Λ j i * ((y i).val : R))) +
        algebraMap R C (∑ i, Λ j i * ((y i).val : R)) := by ring
    rw [e1]
    exact (Valuation.map_add v _ _).trans (max_le (hU2 j y).le (hv.map_le_one _))
  have h5 := (u5 p C v R hv hpC (Fin r) Λ u hΛ hU1 hU2).2 (fun j => algebraMap R C (dj j))
  have hxu : ∀ j y, algebraMap R C (dj j) * u j y = x j y := fun j y => by
    simp only [hudef]
    rw [mul_inv_cancel_left₀ (hdj0 j)]
  simp only [hxu] at h5
  have hxW : ∀ j, x j ∈ AW.carrier := fun j => hAWc ▸ hxmem j
  have hpow : ∀ (f : (Fin r → ZMod p) → C), f ∈ AW.carrier → ∀ k : ℕ, f ^ k ∈ AW.carrier := by
    intro f hf k
    induction k with
    | zero => rw [pow_zero]; exact AW.one_mem
    | succ k ih => rw [pow_succ]; exact AW.mul_mem _ _ ih hf
  have hmon : ∀ α : Fin r → ZMod p, (fun y => ∏ j, x j y ^ (α j).val) ∈ AW.carrier := by
    intro α
    have key : ∀ s : Finset (Fin r), (∏ j ∈ s, x j ^ (α j).val) ∈ AW.carrier := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.prod_empty]; exact AW.one_mem
      | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        exact AW.mul_mem _ _ (hpow _ (hxW a) _) ih
    convert key Finset.univ using 1
    funext y
    simp [Finset.prod_apply]
  obtain ⟨B, hBu, hBc⟩ := AW.lat
  have hcol : ∀ α : Fin r → ZMod p, ∃ c : (Fin r → ZMod p) → R,
      ∑ j', c j' • (fun y => B y j') = fun y => ∏ j, x j y ^ (α j).val := by
    intro α
    have h1 := hmon α
    rw [hBc] at h1
    exact (Submodule.mem_span_range_iff_exists_fun R).1 h1
  choose c hc using hcol
  have hMon : (Matrix.of fun (y α : Fin r → ZMod p) => ∏ j, x j y ^ (α j).val) =
      B * Matrix.of fun j' α => algebraMap R C (c α j') := by
    ext y α
    have e := congrFun (hc α) y
    simp only [Finset.sum_apply, Pi.smul_apply] at e
    rw [Matrix.of_apply, ← e, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j' _ => ?_
    simp only [Matrix.of_apply, Algebra.smul_def]
    ring
  have hvMon : v (Matrix.of fun (y α : Fin r → ZMod p) => ∏ j, x j y ^ (α j).val).det ≤ v B.det := by
    rw [hMon, Matrix.det_mul, map_mul]
    calc v B.det * v (Matrix.of fun j' α => algebraMap R C (c α j')).det ≤ v B.det * 1 :=
          mul_le_mul' le_rfl (IsIntegralMat.det_le_one (v := v) fun j' α => hv.map_le_one _)
      _ = v B.det := mul_one _
  have hColen : HasColen R v AW.carrier (v B.det) := ⟨B, hBc, rfl⟩
  have hN : ∀ y : Fin r → ZMod p, p • y = 0 := by
    intro y
    funext i
    simp [nsmul_eq_mul, ZMod.natCast_self]
  have h4 := u4 p C v R hv hpC (Fin r → ZMod p) hN AW (v B.det) _ hColen hOm
  have hcard : Fintype.card (Fin r → ZMod p) = p ^ r := by simp
  rw [hcard] at h4
  set Y := ∏ j, v (algebraMap R C (dj j)) with hYdef
  set K := p ^ (Fintype.card (Fin r) - 1) * (p * (p - 1) / 2) with hKdef
  have hYK : Y ^ K ≤ v B.det := by
    rw [hYdef, ← Finset.prod_pow]
    exact h5 ▸ hvMon
  have hchain : Y ^ (2 * K) ≤ (v (algebraMap R C cp) ^ d) ^ (p ^ r * (p - 1)) := by
    calc Y ^ (2 * K) = (Y ^ K) ^ 2 := by rw [← pow_mul, mul_comm]
      _ ≤ v B.det ^ 2 := by gcongr
      _ ≤ (v (algebraMap R C (p : R)) ^ d) ^ p ^ r := h4
      _ = (v (algebraMap R C cp) ^ d) ^ (p ^ r * (p - 1)) := by
        rw [← hSet.cp_val, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
  rw [hXeq]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hY1 : Y = 1 := by simp [hYdef]
    rw [hY1] at hchain ⊢
    rw [one_pow] at hchain
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      simp
    · exfalso
      have hlt : (v (algebraMap R C cp) ^ d) ^ (p ^ 0 * (p - 1)) < 1 := by
        refine pow_lt_one₀ zero_le' (pow_lt_one₀ zero_le' ?_ (by omega)) (by simp; omega)
        have h1 := hSet.cp_val
        by_contra hge
        push_neg at hge
        have h2 : 1 ≤ v (algebraMap R C cp) ^ (p - 1) := one_le_pow₀ hge
        rw [h1] at h2
        exact absurd hSet.p_lt (not_lt.2 h2)
      exact absurd hchain (not_le.2 hlt)
  · have h2K : 2 * K = p ^ r * (p - 1) := by
      rw [hKdef, Fintype.card_fin, ← mul_assoc, mul_comm 2, mul_assoc,
        Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self p)]
      have : p ^ (r - 1) * p = p ^ r := by rw [← pow_succ]; congr 1; omega
      rw [← mul_assoc, this]
    rw [h2K] at hchain
    exact (pow_le_pow_iff_left₀ zero_le' zero_le' (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega))).1 hchain

end ReciprocityTheory.PGsh.Up
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.PullbackHopfOrder

private theorem red_surj {p : ℕ} [Fact p.Prime] {g : ℕ} (n : Nb p g) : ∃ t, red p g t = n := by
  refine ⟨fun i => ((n i).val : ℤ_[p]), funext fun i => ?_⟩
  simp [red]

private theorem red_mulVec {p : ℕ} [Fact p.Prime] {g : ℕ} (M : Matrix (Ix g) (Ix g) ℤ_[p])
    (t : TT p g) : red p g (M *ᵥ t) = M.map PadicInt.toZMod *ᵥ red p g t := by
  funext i
  simp [red, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem restrict_hopfOrder_length : RestrictedHopfOrderStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H a ha r Bw hrange hkerB d hd
  have hE : H.ρ a * H.ρ a = H.ρ a := by rw [← map_mul, ha]
  have hcol : ∀ j : Ix g, ∃ k : Fin r → ℤ_[p], Bw *ᵥ k = H.ρ a *ᵥ Pi.single j 1 := by
    intro j
    have hm : H.ρ a *ᵥ Pi.single j 1 ∈ LinearMap.range (Matrix.mulVecLin Bw) := by
      rw [hrange]
      exact ⟨Pi.single j 1, rfl⟩
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, hk⟩
  choose kk hkk using hcol
  let K : Matrix (Fin r) (Ix g) ℤ_[p] := Matrix.of fun i j => kk j i
  have hBK : Bw * K = H.ρ a := by
    ext i j
    have h1 : (Bw * K) i j = (Bw *ᵥ kk j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, K]
    rw [h1, hkk j]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hKB : K * Bw = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    apply LinearMap.ker_eq_bot.mp hkerB
    show Bw *ᵥ ((K * Bw) *ᵥ x) = Bw *ᵥ x
    obtain ⟨y, hy⟩ : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin (H.ρ a)) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBK, ← hy]
    show H.ρ a *ᵥ (H.ρ a *ᵥ y) = H.ρ a *ᵥ y
    rw [Matrix.mulVec_mulVec, hE]
  let ψ := psiW Bw
  let χ : Nb p g →+ (Fin r → ZMod p) := (Matrix.mulVecLin (K.map PadicInt.toZMod)).toAddMonoidHom
  have hχψ : ∀ x, χ (ψ x) = x := by
    intro x
    show K.map PadicInt.toZMod *ᵥ (Bw.map PadicInt.toZMod *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hKB, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hred : ∀ t, ψ (χ (red p g t)) = red p g (H.ρ a *ᵥ t) := by
    intro t
    show Bw.map PadicInt.toZMod *ᵥ (K.map PadicInt.toZMod *ᵥ red p g t) = _
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hBK, ← red_mulVec]
  have hA : ∀ f ∈ H.AA.carrier, (fun n => f (ψ (χ n))) ∈ H.AA.carrier := by
    intro f hf
    obtain ⟨f', hf', hff⟩ := H.h3 a f hf
    convert hf' using 1
    funext n
    obtain ⟨t, rfl⟩ := red_surj n
    rw [hff, hred]
  have hinj : Function.Injective ψ := fun x y h => by rw [← hχψ x, ← hχψ y, h]
  have hEE : H.ρL a * H.ρL a = H.ρL a := by rw [← map_mul, ha]
  let e := hd.some
  let Q1 : Matrix (Fin g) (Fin d) R :=
    LinearMap.toMatrix' ((LinearMap.range (H.ρL a).mulVecLin).subtype ∘ₗ e.symm.toLinearMap)
  let Q2 : Matrix (Fin d) (Fin g) R :=
    LinearMap.toMatrix' (e.toLinearMap ∘ₗ (H.ρL a).mulVecLin.rangeRestrict)
  have hQ12 : Q1 * Q2 = H.ρL a := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun x => ?_
    simp [Matrix.toLin'_apply]
  have hQ21 : Q2 * Q1 = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    refine LinearMap.ext fun y => ?_
    have hz : (H.ρL a).mulVecLin.rangeRestrict ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) =
        e.symm y := by
      apply Subtype.ext
      obtain ⟨w, hw⟩ := (e.symm y).2
      show H.ρL a *ᵥ ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) = e.symm y
      rw [← hw]
      show H.ρL a *ᵥ (H.ρL a *ᵥ w) = H.ρL a *ᵥ w
      rw [Matrix.mulVec_mulVec, hEE]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, LinearMap.id_apply]
    rw [hz, LinearEquiv.apply_symm_apply]
  have hF : Q2ᵀ * Q1ᵀ = (H.ρL a)ᵀ := by rw [← Matrix.transpose_mul, hQ12]
  have h21 : Q1ᵀ * Q2ᵀ = 1 := by rw [← Matrix.transpose_mul, hQ21, Matrix.transpose_one]
  obtain ⟨eO⟩ := omega_pull p ψ χ hχψ H.AA.carrier hA H.φ H.cotangent_surjective H.cotangent_ker_eq (H.ρL a)ᵀ Q2ᵀ Q1ᵀ hF h21
    (fun f f' l hff hl => H.cotangent_linear a f f' l (fun t => by rw [hff, hred]) hl)
  refine ⟨pullHopf ψ H.AA (isLat_pull v hS.integers ψ hinj H.AA), pullHopf_carrier _ _ _, ?_⟩
  rw [pullHopf_carrier]
  exact ⟨d, fun _ => (p : R), ⟨eO.trans (qPi p d)⟩, by simp [Finset.prod_const]⟩

end ReciprocityTheory.PGsh.Up
end
end

section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

private lemma smulMV2 {R : Type} [CommRing R] {κ μ : Type} [Fintype μ] (c : R) (M : Matrix κ μ R)
    (v : μ → R) : (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext k; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem smith_normal_form_statement : EigenQuotientSmithStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π horth hσ hsT hPT hsL hPL w hw r Bw hrange
    hker X hX
  haveI : IsDomain R := htd_domain hS
  have hv := hS.integers
  have hcp : cp ≠ 0 := htd_cp_ne hS
  set ι := algebraMap ℤ_[p] R with hι
  have hidw : H.ρ (e w) * H.ρ (e w) = H.ρ (e w) := by rw [← map_mul, horth, if_pos rfl]
  obtain ⟨L, hLB, hBL⟩ := PullbackHopfOrder.exists_split (H.ρ (e w)) hidw Bw hrange hker
  set B := Bw.map ι with hB
  set εw := (H.ρ (e w)).map ι with hεw
  have hLB' : L.map ι * B = 1 := by rw [hB, ← Matrix.map_mul, hLB, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hBL' : B * L.map ι = εw := by rw [hB, ← Matrix.map_mul, hBL]
  have hεB : εw * B = B := by
    rw [← hBL', Matrix.mul_assoc, hLB', Matrix.mul_one]
  set Φ := phiP H e with hΦ
  set M := Φ * B with hM
  obtain ⟨hform, hblock, hPblock⟩ := btP_facts hS H e π horth hσ hsT hPT hsL hPL
  have hJ := phiP_J hS H e π horth hσ hsT hPT hsL hPL
  obtain ⟨-, -, hEdet⟩ := htd_E H
  set E' := H.E.map ι with hE'
  have hdetΦ : Φ.det ≠ 0 := by
    intro h0
    have h := det_sq_eq E' Φ cp hJ
    rw [h0, zero_pow two_ne_zero] at h
    have hne : cp ^ (2 * g) * (E'.det * (stdJ R g).det) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hcp) (mul_ne_zero hEdet.ne_zero isUnit_det_stdJ.ne_zero)
    exact hne h.symm
  have hΦinj : ∀ x, Φ *ᵥ x = 0 → x = 0 := by
    intro x hx
    have h1 : Φ.det • x = 0 := by
      have h2 : (Φ.adjugate * Φ) *ᵥ x = Φ.det • x := by rw [adjugate_mul, smulMV2, one_mulVec]
      rw [← h2, ← mulVec_mulVec, hx, mulVec_zero]
    exact (smul_eq_zero.1 h1).resolve_left hdetΦ
  have hMinj : ∀ t, M *ᵥ t = 0 → t = 0 := by
    intro t ht
    have h1 : B *ᵥ t = 0 := hΦinj _ (by rw [mulVec_mulVec]; exact ht)
    rw [← one_mulVec t, ← hLB', ← mulVec_mulVec, h1, mulVec_zero]

  set Φp := E'⁻¹ * Φᵀ * stdJ R g with hΦp
  have hΦpΦ : Φp * Φ = cp • (1 : Matrix (Ix g) (Ix g) R) := by
    rw [hΦp, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Φᵀ, hJ, Matrix.mul_smul,
      nonsing_inv_mul _ hEdet]
  have hΦΦp : Φ * Φp = cp • (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) := by
    have h1 : (Φ * Φp - cp • 1) * Φ = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hΦpΦ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h2 : Φ.det • (Φ * Φp - cp • 1) = 0 := by
      calc Φ.det • (Φ * Φp - cp • 1) = (Φ * Φp - cp • 1) * (Φ.det • 1) := by
            rw [Matrix.mul_smul, Matrix.mul_one]
        _ = (Φ * Φp - cp • 1) * (Φ * Φ.adjugate) := by rw [mul_adjugate]
        _ = ((Φ * Φp - cp • 1) * Φ) * Φ.adjugate := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [h1, Matrix.zero_mul]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hdetΦ)

  set Pw : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R :=
    fromBlocks (H.ρL (e (π w)))ᵀ 0 0 (H.ρL (e w)) with hPw
  have hidL : ∀ a : O, a * a = a → H.ρL a * H.ρL a = H.ρL a := fun a ha => by rw [← map_mul, ha]
  have hidwL := hidL (e w) (by rw [horth, if_pos rfl])
  have hidwbL := hidL (e (π w)) (by rw [horth, if_pos rfl])
  have hPwmv : ∀ q, Pw *ᵥ q = Sum.elim ((H.ρL (e (π w)))ᵀ *ᵥ (q ∘ Sum.inl))
      (H.ρL (e w) *ᵥ (q ∘ Sum.inr)) := by
    intro q
    rw [hPw, ← Sum.elim_comp_inl_inr q, fromBlocks_mulVec]
    simp
  have hΦεw : Φ * εw = Pw * Φ := by
    have e1 : H.Ht * εw = (H.ρL (e (π w)))ᵀ * H.Ht := by rw [hεw, H.Ht_equivariant.1 (e w), hσ w]
    rw [hΦ, phiP, fromRows_mul, e1, hblock w]
    ext i j
    rcases i with i | i
    · simp [hPw, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]
    · simp [hPw, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks]
  have hrangeP : ∀ (P : Matrix (Fin g) (Fin g) R), P * P = P → ∀ x,
      x ∈ LinearMap.range (Matrix.mulVecLin P) ↔ P *ᵥ x = x := by
    intro P hP x
    constructor
    · rintro ⟨y, rfl⟩
      show P *ᵥ (P *ᵥ y) = P *ᵥ y
      rw [mulVec_mulVec, hP]
    · intro hx; exact ⟨x, hx⟩
  have hidT : (H.ρL (e (π w)))ᵀ * (H.ρL (e (π w)))ᵀ = (H.ρL (e (π w)))ᵀ := by
    rw [← transpose_mul, hidwbL]
  have hQw : ∀ q, q ∈ qW H (e w) (e (π w)) ↔ Pw *ᵥ q = q := by
    intro q
    show (q ∘ Sum.inl ∈ lieDPart H (e (π w)) ∧ q ∘ Sum.inr ∈
      LinearMap.range (Matrix.mulVecLin (H.ρL (e w)))) ↔ _
    rw [show lieDPart H (e (π w)) = LinearMap.range (Matrix.mulVecLin (H.ρL (e (π w)))ᵀ) from rfl,
      hrangeP _ hidT, hrangeP _ hidwL, hPwmv]
    constructor
    · rintro ⟨h1, h2⟩
      rw [h1, h2]; exact Sum.elim_comp_inl_inr q
    · intro h
      exact ⟨by rw [← h] at *; funext k; exact (congrFun h (Sum.inl k)),
        by funext k; exact congrFun h (Sum.inr k)⟩

  have hmapT : (tPart H (e w)).map (Matrix.mulVecLin Φ) = LinearMap.range (Matrix.mulVecLin M) := by
    ext q
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨L.map ι *ᵥ x, ?_⟩
      show M *ᵥ (L.map ι *ᵥ x) = Φ *ᵥ (εw *ᵥ x)
      rw [hM, ← mulVec_mulVec, mulVec_mulVec (M := B), hBL']
    · rintro ⟨t, rfl⟩
      refine ⟨εw *ᵥ (B *ᵥ t), ⟨B *ᵥ t, rfl⟩, ?_⟩
      show Φ *ᵥ (εw *ᵥ (B *ᵥ t)) = M *ᵥ t
      rw [mulVec_mulVec (M := εw), hεB, hM, mulVec_mulVec]
  have hMQ : ∀ t, Pw *ᵥ (M *ᵥ t) = M *ᵥ t := by
    intro t
    rw [hM, ← mulVec_mulVec, mulVec_mulVec (M := Pw), ← hΦεw, ← mulVec_mulVec, mulVec_mulVec (M := εw), hεB]
  have hkillQ : ∀ q, Pw *ᵥ q = q → ∃ t, M *ᵥ t = cp • q := by
    intro q hq
    refine ⟨L.map ι *ᵥ (εw *ᵥ (Φp *ᵥ q)), ?_⟩
    have hεε : εw * εw = εw := by rw [hεw, ← Matrix.map_mul, hidw]
    rw [hM, ← mulVec_mulVec, mulVec_mulVec (M := B), hBL', mulVec_mulVec (M := εw), hεε, mulVec_mulVec (M := Φ),
      hΦεw, ← mulVec_mulVec, mulVec_mulVec (M := Φ), hΦΦp, smulMV2, one_mulVec, mulVec_smul, hq]
  have hsat : ∀ q (c : R), c ≠ 0 → Pw *ᵥ (c • q) = c • q → Pw *ᵥ q = q := by
    intro q c hc h
    rw [mulVec_smul] at h
    exact smul_right_injective _ hc h

  set e2 : Fin g ⊕ Fin g ≃ Fin (g + g) := finSumFinEquiv with he2
  set M' : Matrix (Fin (g + g)) (Fin r) R := M.submatrix e2.symm id with hM'
  have hM'v : ∀ t, M' *ᵥ t = (M *ᵥ t) ∘ e2.symm := fun t => by
    funext j; simp [hM', Matrix.mulVec, dotProduct]
  obtain ⟨P, Q, a, hPu, hQu, hD⟩ := Smith.smith_mat hv (g + g) r M'
  set D := P * M' * Q with hDdef
  have hDv : ∀ t (j : Fin (g + g)), (D *ᵥ t) j = if h : (j : ℕ) < r then a j * t ⟨j, h⟩ else 0 := by
    intro t j
    simp only [Matrix.mulVec, dotProduct, hD, ite_mul, zero_mul]
    exact sum_val_eq (j : ℕ) (fun k => a j * t k)
  have hQQ : ∀ t, Q *ᵥ (Q⁻¹ *ᵥ t) = t := fun t => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hQu, one_mulVec]
  have hQQ' : ∀ t, Q⁻¹ *ᵥ (Q *ᵥ t) = t := fun t => by
    rw [mulVec_mulVec, nonsing_inv_mul _ hQu, one_mulVec]
  have hPP : ∀ t, P *ᵥ (P⁻¹ *ᵥ t) = t := fun t => by
    rw [mulVec_mulVec, mul_nonsing_inv _ hPu, one_mulVec]
  have hPP' : ∀ t, P⁻¹ *ᵥ (P *ᵥ t) = t := fun t => by
    rw [mulVec_mulVec, nonsing_inv_mul _ hPu, one_mulVec]
  have hM'D : ∀ t, P *ᵥ (M' *ᵥ t) = D *ᵥ (Q⁻¹ *ᵥ t) := fun t => by
    rw [hDdef, ← mulVec_mulVec, ← mulVec_mulVec, hQQ]
  have hMzero : ∀ t, M' *ᵥ t = 0 → t = 0 := by
    intro t ht
    apply hMinj
    funext x
    have h1 := congrFun ht (e2 x)
    rw [hM'v] at h1
    simpa using h1
  have hDz : ∀ s, D *ᵥ s = 0 → s = 0 := by
    intro s hs
    have h1 : M' *ᵥ (Q *ᵥ s) = 0 := by
      rw [← hPP' (M' *ᵥ (Q *ᵥ s)), hM'D, hQQ', hs, mulVec_zero]
    rw [← hQQ' s, hMzero _ h1, mulVec_zero]
  have hsingle_ne : ∀ {n : ℕ} (k : Fin n), (Pi.single k (1 : R) : Fin n → R) ≠ 0 := by
    intro n k h
    have h1 := congrFun h k
    simp at h1
  have hrle : ∀ k : Fin r, (k : ℕ) < g + g := by
    intro k
    by_contra hk
    apply hsingle_ne k
    apply hDz
    funext j
    rw [hDv]
    split_ifs with h
    · rw [Pi.single_eq_of_ne]
      · simp
      · intro hjk; apply hk; rw [← hjk]; exact j.isLt
    · rfl
  set dj : Fin r → R := fun k => a ⟨k, hrle k⟩ with hdj
  have hDsingle : ∀ k : Fin r, D *ᵥ Pi.single k 1 = dj k • Pi.single (⟨k, hrle k⟩ : Fin (g + g)) 1 := by
    intro k
    funext j
    rw [hDv]
    by_cases hjk : (j : ℕ) = k
    · have hj : j = ⟨k, hrle k⟩ := Fin.ext hjk
      subst hj
      rw [dif_pos k.isLt]
      simp [hdj]
    · rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hjk (by rw [h])), smul_zero]
      split_ifs with h
      · rw [Pi.single_eq_of_ne (fun h' => hjk (by rw [← h'])), mul_zero]
      · rfl
  have ha0 : ∀ k, dj k ≠ 0 := by
    intro k hk
    apply hsingle_ne k
    apply hDz
    rw [hDsingle, hk, zero_smul]
  refine ⟨Q⁻¹, dj, isUnit_nonsing_inv_det Q hQu, ?_, ?_, ?_⟩
  ·
    intro k
    have hDQ : D * Q⁻¹ = P * M' := by
      rw [hDdef, Matrix.mul_assoc, mul_nonsing_inv _ hQu, Matrix.mul_one]
    have h1 : dj k • (Q⁻¹) k = (D * Q⁻¹) ⟨k, hrle k⟩ := by
      funext i
      simp only [Matrix.mul_apply, hD, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · simp [hdj]
      · intro b _ hb
        rw [if_neg (fun h => hb (Fin.ext h)), zero_mul]
      · intro h; exact absurd (Finset.mem_univ k) h
    rw [h1, hDQ]
    have h3 : (P * M') ⟨k, hrle k⟩ = ∑ l, P ⟨k, hrle k⟩ l • (fun i => M (e2.symm l) i) := by
      funext i
      simp [Matrix.mul_apply, Finset.sum_apply, hM']
    rw [h3]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨e2.symm l, rfl⟩)
  ·
    intro k
    set j : Fin (g + g) := ⟨k, hrle k⟩
    set u := P⁻¹ *ᵥ Pi.single j 1
    have hu : M *ᵥ (Q *ᵥ Pi.single k 1) = dj k • (u ∘ e2) := by
      funext x
      have h1 : M' *ᵥ (Q *ᵥ Pi.single k 1) = dj k • u := by
        rw [← hPP' (M' *ᵥ _), hM'D, hQQ', hDsingle, mulVec_smul]
      have h2 := congrFun h1 (e2 x)
      rw [hM'v] at h2
      simpa using h2
    have hsatu : Pw *ᵥ (u ∘ e2) = u ∘ e2 :=
      hsat (u ∘ e2) (dj k) (ha0 k) (by rw [← hu]; exact hMQ _)
    obtain ⟨t, ht⟩ := hkillQ _ hsatu
    have h3 : D *ᵥ (Q⁻¹ *ᵥ t) = cp • Pi.single j 1 := by
      rw [← hM'D, hM'v, ht]
      have : (cp • (u ∘ ⇑e2)) ∘ ⇑e2.symm = cp • u := by funext y; simp
      rw [this, mulVec_smul, hPP]
    have h4 := congrFun h3 j
    rw [hDv, dif_pos k.isLt] at h4
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h4
    apply hv.le_of_dvd
    exact ⟨_, h4.symm⟩
  ·
    let F : qW H (e w) (e (π w)) →ₗ[R] ((k : Fin r) → R ⧸ Ideal.span {dj k}) :=
      LinearMap.pi fun k => (Submodule.mkQ (Ideal.span {dj k})) ∘ₗ
        (LinearMap.proj (⟨k, hrle k⟩ : Fin (g + g))) ∘ₗ P.mulVecLin ∘ₗ
        (LinearMap.funLeft R R e2.symm) ∘ₗ (qW H (e w) (e (π w))).subtype
    have hF : ∀ q k, F q k = Ideal.Quotient.mk _
        ((P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm)) ⟨k, hrle k⟩) := fun q k => rfl
    have hker : LinearMap.ker F =
        (LinearMap.range (Matrix.mulVecLin M)).comap (qW H (e w) (e (π w))).subtype := by
      ext q
      rw [LinearMap.mem_ker, Submodule.mem_comap]
      constructor
      · intro hq
        have hq' : ∀ k, (P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm)) ⟨k, hrle k⟩ ∈ Ideal.span {dj k} :=
          fun k => Ideal.Quotient.eq_zero_iff_mem.1 ((hF q k).symm.trans (congrFun hq k))
        choose s hs using fun k => Ideal.mem_span_singleton'.1 (hq' k)
        obtain ⟨t, ht⟩ := hkillQ q ((hQw q).1 q.2)
        have hhigh : ∀ j : Fin (g + g), ¬ (j : ℕ) < r →
            (P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm)) j = 0 := by
          intro j hj
          have h1 : D *ᵥ (Q⁻¹ *ᵥ t) = cp • (P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm)) := by
            rw [← hM'D, hM'v, ht, ← mulVec_smul]
            rfl
          have h2 := congrFun h1 j
          rw [hDv, dif_neg hj, Pi.smul_apply, smul_eq_mul] at h2
          exact (mul_eq_zero.1 h2.symm).resolve_left hcp
        have hPq : P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm) = D *ᵥ s := by
          funext j
          rw [hDv]
          split_ifs with h
          · rw [← hs ⟨j, h⟩, mul_comm]
          · exact hhigh j h
        refine ⟨Q *ᵥ s, ?_⟩
        funext x
        have h1 : M' *ᵥ (Q *ᵥ s) = (q : Fin g ⊕ Fin g → R) ∘ e2.symm := by
          rw [← hPP' (M' *ᵥ _), hM'D, hQQ', ← hPq, hPP']
        have h2 := congrFun h1 (e2 x)
        rw [hM'v] at h2
        simpa using h2
      · rintro ⟨t, ht⟩
        funext k
        rw [hF]
        apply Ideal.Quotient.eq_zero_iff_mem.2
        have h1 : P *ᵥ ((q : Fin g ⊕ Fin g → R) ∘ e2.symm) = D *ᵥ (Q⁻¹ *ᵥ t) := by
          rw [← hM'D, hM'v]
          congr 1
          exact congrArg (· ∘ e2.symm) ht.symm
        rw [h1, hDv, dif_pos k.isLt]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have hsurj : Function.Surjective F := by
      intro z
      set y : Fin r → R := fun k => Quotient.out (z k)
      set α : R := ∏ k, dj k
      have hα : α ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => ha0 k
      set yt : Fin (g + g) → R := fun j => if h : (j : ℕ) < r then y ⟨j, h⟩ else 0
      set u := P⁻¹ *ᵥ yt
      set s : Fin r → R := fun k => (∏ l ∈ Finset.univ.erase k, dj l) * y k
      have hDs : D *ᵥ s = α • yt := by
        funext j
        rw [hDv]
        split_ifs with h
        · simp only [Pi.smul_apply, smul_eq_mul, yt, dif_pos h, s, α]
          rw [← Finset.mul_prod_erase Finset.univ dj (Finset.mem_univ ⟨j, h⟩)]
          simp only [hdj]
          ring
        · simp [yt, dif_neg h]
      have hαu : M *ᵥ (Q *ᵥ s) = α • (u ∘ e2) := by
        funext x
        have h1 : M' *ᵥ (Q *ᵥ s) = α • u := by
          rw [← hPP' (M' *ᵥ _), hM'D, hQQ', hDs, mulVec_smul]
        have h2 := congrFun h1 (e2 x)
        rw [hM'v] at h2
        simpa using h2
      have hu : Pw *ᵥ (u ∘ e2) = u ∘ e2 := hsat _ α hα (by rw [← hαu]; exact hMQ _)
      refine ⟨⟨u ∘ e2, (hQw _).2 hu⟩, ?_⟩
      funext k
      rw [hF]
      have h1 : ((u ∘ ⇑e2) ∘ ⇑e2.symm) = u := by funext j; simp
      show Ideal.Quotient.mk _ ((P *ᵥ ((u ∘ ⇑e2) ∘ ⇑e2.symm)) ⟨k, hrle k⟩) = z k
      rw [h1, hPP]
      simp only [yt, dif_pos k.isLt, Fin.eta, y]
      exact Ideal.Quotient.mk_out (z k)
    have heq : xMod H e π w ≃ₗ[R] ((k : Fin r) → R ⧸ Ideal.span {dj k}) :=
      (Submodule.quotEquivOfEq _ _ (by rw [hmapT, hker])).trans (F.quotKerEquivOfSurjective hsurj)
    exact hasLen_unique hv hX ⟨r, dj, ⟨heq⟩, rfl⟩

end ReciprocityTheory.PGsh.Up
end
end

section
namespace ReciprocityTheory.PGsh.Up

theorem lengthDegree_of_wdet_frobenius (hU6 : CokernelLengthComparisonStatement) (hU7 : UnramifiedCokernelLengthStatement) : CokernelLowerBoundStatement :=
  cokernelLowerBound_of hU6 hU7 lenEx killedGen idemGen


end ReciprocityTheory.PGsh.Up
end

section
namespace ReciprocityTheory.PGsh.Up

theorem wdet_of_smith_normal_form (hS : EigenQuotientSmithStatement) : CokernelLengthComparisonStatement :=
  cokernelLengthComparison_of wdetLen (wdetDegree_of_smith_restrict hS restrict_hopfOrder_length restrictedHopfOrderApproximation)

theorem u6 : CokernelLengthComparisonStatement := wdet_of_smith_normal_form smith_normal_form_statement

end ReciprocityTheory.PGsh.Up
end
