import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm

noncomputable section

open WittVector Ideal Matrix

namespace GlobalTheory.Sandwich.Model

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

theorem xi_eq (ε : PreTilt O p) : xi ε = ReciprocityTheory.PGsh.Ainf.xi p O ε := rfl

theorem nu_eq (ε : PreTilt O p) : nu ε = ReciprocityTheory.PGsh.Ainf.nu p O ε := rfl

def mixed (ε : PreTilt O p) (h : ℕ) (S : Finset (Fin h)) : Datum ε h (Fin h → ℤ_[p]) where
  F := diagonal fun i => if i ∈ S then mu ε else 1
  G := diagonal fun i => if i ∈ S then 1 else mu ε
  Ψ := diagonal fun i => if i ∈ S then xi ε else 1
  Ψ' := diagonal fun i => if i ∈ S then 1 else xi ε
  ρT := Matrix.diagonalAlgHom ℤ_[p]
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (Matrix.diagonalRingHom _ _)
  G_mul_F := by
    rw [diagonal_mul_diagonal, smul_one_eq_diagonal]
    refine congrArg diagonal (funext fun i => ?_); split_ifs <;> simp
  F_eq := by
    rw [diagonal_map (map_zero _), diagonal_mul_diagonal]
    refine congrArg diagonal (funext fun i => ?_)
    split_ifs <;> simp [phiInv_mu, xi_mul_nu]
  Ψ_mul := by
    rw [diagonal_mul_diagonal, smul_one_eq_diagonal]
    refine congrArg diagonal (funext fun i => ?_); split_ifs <;> simp
  F_act := by
    intro a
    simp [diagonal_map (map_zero _), diagonal_mul_diagonal, mul_comm]


theorem mixed_bb (ε : PreTilt O p) (hμ : fontaineTheta O p (mu ε) = 0) (h : ℕ) (S : Finset (Fin h))
    (x : Fin h → O) (i : Fin h) : (mixed ε h S).bb x i = if i ∈ S then x i else 0 := by
  simp only [Datum.bb, mixed, diagonal_map (map_zero _), toLin'_apply, mulVec_diagonal]
  split_ifs <;> simp [hμ]

theorem mem_mixed_Fil (ε : PreTilt O p) (hμ : fontaineTheta O p (mu ε) = 0) (h : ℕ)
    (S : Finset (Fin h)) (x : Fin h → O) : x ∈ (mixed ε h S).Fil ↔ ∀ i ∈ S, x i = 0 := by
  rw [Datum.Fil, LinearMap.mem_ker, funext_iff]
  simp only [mixed_bb ε hμ]
  constructor
  · intro H i hi; simpa [hi] using H i
  · intro H i; split_ifs with hi
    · exact H i hi
    · rfl

section Field

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

theorem theta_mu : fontaineTheta O p (mu ε) = 0 := by
  rw [← xi_mul_nu, map_mul, xi_eq, ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε, zero_mul]

theorem mu_ne_zero : mu ε ≠ 0 := by
  intro h
  rw [← xi_mul_nu, mul_comm] at h
  have := ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε _ h
  exact ReciprocityTheory.PGsh.Ainf.theta_nu p O hv ε hε (by rw [← nu_eq, this, map_zero])

omit hε [IsAlgClosed C] in
theorem isDomain_Ainf : IsDomain (Ainf p O) := by
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  infer_instance

variable {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)

theorem F_mul_G : D.F * D.G = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) := by
  haveI := isDomain_Ainf (p := p) hv
  have hd : D.F.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det D.G_mul_F
    rw [det_mul, h0, mul_zero, det_smul, det_one, mul_one] at this
    exact pow_ne_zero _ (mu_ne_zero hv hε) this.symm
  have h1 : (D.F * D.G - mu ε • 1) * D.F = 0 := by
    rw [sub_mul, mul_assoc, D.G_mul_F]; simp
  have h2 := congrArg (· * D.F.adjugate) h1
  simp only [mul_assoc, mul_adjugate, zero_mul, Matrix.mul_smul, mul_one] at h2
  refine sub_eq_zero.1 (Matrix.ext fun i j => ?_)
  have h3 : D.F.det * (D.F * D.G - mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) i j = 0 :=
    congrFun (congrFun h2 i) j
  exact (mul_eq_zero.1 h3).resolve_left hd





theorem bound_aux (X Y : Matrix (Fin h) (Fin h) (Ainf p O)) (hXY : X * Y = mu ε • 1)
    (x : Fin h → O) (hx : Y.map (fontaineTheta O p) *ᵥ x = 0) :
    ∃ y, X.map (fontaineTheta O p) *ᵥ y = fontaineTheta O p (nu ε) • x := by
  choose m hm using fun i => ReciprocityTheory.PGsh.Ainf.theta_surj p O hv (x i)
  have h1 : ∀ i, ∃ c, (Y *ᵥ m) i = xi ε * c := by
    intro i
    have : (Y *ᵥ m) i ∈ RingHom.ker (fontaineTheta O p) := by
      rw [RingHom.mem_ker, RingHom.map_mulVec]
      have : (fontaineTheta O p) ∘ m = x := funext hm
      rw [this, hx]; rfl
    rw [ReciprocityTheory.PGsh.Ainf.ker_theta p O hv ε hε, Ideal.mem_span_singleton] at this
    exact this
  choose c hc using h1
  have h2 : Y *ᵥ m = xi ε • c := funext hc
  have h3 : ∀ i, (X *ᵥ c) i = nu ε * m i := by
    intro i
    have h4 := congrFun (congrArg (X *ᵥ ·) h2) i
    simp only [mulVec_mulVec, hXY, mulVec_smul, smul_mulVec, one_mulVec, Pi.smul_apply,
      smul_eq_mul] at h4
    refine sub_eq_zero.1 (ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε _ ?_)
    rw [← xi_eq, ← xi_mul_nu] at *
    linear_combination -h4
  refine ⟨fontaineTheta O p ∘ c, funext fun i => ?_⟩
  rw [← RingHom.map_mulVec, h3, map_mul, hm]; rfl



end Field

end GlobalTheory.Sandwich.Model
