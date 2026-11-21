import Formalism.LocalToGlobal.GaloisLevelStructure.NGalTied
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

section
noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual NumberField IsDedekindDomain Polynomial

namespace Formalism.L2.NR

section frame

variable {E Ω L : Type} [Field E] [Field Ω] [Algebra E Ω] [Field L]

def FrameOver (j : E ≃+* L) (k : AlgebraicClosure L ≃+* Ω) : Prop :=
  ∀ x : E, k (algebraMap L (AlgebraicClosure L) (j x)) = algebraMap E Ω x

def toRec (j : E ≃+* L) (k : AlgebraicClosure L ≃+* Ω) (hk : FrameOver j k) :
    (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) →* (Ω ≃ₐ[E] Ω) where
  toFun σ := AlgEquiv.ofRingEquiv (f := (k.symm.trans (σ : AlgebraicClosure L ≃+* AlgebraicClosure L)).trans k)
    (fun x => by
      simp only [RingEquiv.trans_apply]
      rw [← hk x, RingEquiv.symm_apply_apply]
      simp)
  map_one' := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    simp


def ofRec (j : E ≃+* L) (k : AlgebraicClosure L ≃+* Ω) (hk : FrameOver j k) :
    (Ω ≃ₐ[E] Ω) →* (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) where
  toFun g := AlgEquiv.ofRingEquiv (f := (k.trans (g : Ω ≃+* Ω)).trans k.symm)
    (fun y => by
      have h := hk (j.symm y)
      rw [RingEquiv.apply_symm_apply] at h
      simp only [RingEquiv.trans_apply]
      rw [h]
      simp only [AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
      rw [← h, RingEquiv.symm_apply_apply])
  map_one' := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    simp




end frame

def IsRepOfSigI (D : D7) (ℓ : ℕ) [Fact ℓ.Prime] (ι : Qbar ℓ ≃+* ℂ) (b : ℕ) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar ℓ)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin b) (Qbar ℓ)) : Matrix (Fin b) (Fin b) (Qbar ℓ))) ∧
  Formalism.MainNotions.N.IsSSRep ρ ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((ρ σ : GL _ _) : Matrix (Fin b) (Fin b) (Qbar ℓ)).charpoly.map ι.toRingHom =
      Formalism.MainNotions.N.galPol D.naut (D.naut.lpTw (Formalism.MainNotions.N.isoLoc D.nd D.naut Sig w) ((1 - (b : ℝ)) / 2))

def IsRepOfSigQ (D : D7) (i : D.nd.Loc) (b : ℕ) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))) : Prop :=
  IsRepOfSigI D (D.nd.l i) (D.naut.iotaQC i) b Sig ρ

def InducesPl (D : D7) (lam : D.what₂.places.Pl) {ℓ : ℕ} [Fact ℓ.Prime] (ι : Qbar ℓ ≃+* ℂ) : Prop :=
  ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val lam x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1

def twistRep {Γ K : Type} [Group Γ] [CommRing K] {n : ℕ} (ρ : Γ →* GL (Fin n) K) (χ : Γ →* Kˣ) :
    Γ →* GL (Fin n) K where
  toFun g := Units.map (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom (χ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    have key : ∀ (c : K) (M : Matrix (Fin n) (Fin n) K),
        (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom c * M = M * (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom c :=
      fun c M => Algebra.commutes c M
    ext1
    simp only [map_mul, Units.val_mul, Units.coe_map, mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← key]

theorem twistRep_apply {Γ K : Type} [Group Γ] [CommRing K] {n : ℕ} (ρ : Γ →* GL (Fin n) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((twistRep ρ χ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      algebraMap K (Matrix (Fin n) (Fin n) K) (χ g : K) * (ρ g : Matrix (Fin n) (Fin n) K) := rfl

def IsConjRep {Γ K : Type} [Group Γ] [CommRing K] {n : ℕ} (ρ₁ ρ₂ : Γ →* GL (Fin n) K) : Prop :=
  ∃ P : GL (Fin n) K, ∀ g, ρ₁ g = P * ρ₂ g * P⁻¹

theorem one_le_r (D : D7) : 1 ≤ D.R.r := by
  have := D.R.two_le_m
  show 1 ≤ D.R.k + D.R.m - 1
  omega

def GalRepEx (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)), IsRepOfSigQ D i a [⟨a, π, 1⟩] ρ

def ClassFieldHeckeAlgebraic (D : D7) : Prop :=
  ∀ i (χ : D.naut.CG 1) (s : ℝ), (∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) →
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧
      (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s) ∧
      ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s ∧
        ∀ τ, Formalism.MainNotions.N.InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) =
          (D.naut.infG χ ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ)))

def EtaShiftInt (D : D7) : Prop :=
  ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ, ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ)

def RowPar (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → ∃ Sig : List (Part D.naut.CG),
    Formalism.MainNotions.N.HasParamW D.nd D.naut i σ Sig ∧ (D.nd.goodRow σ → ∀ p ∈ Sig, D.naut.csd p.π ∧ D.naut.ralg p.π)

def IsRowPar (D : D7) (a : D.nd.Loc) (σ : D.what₂.FT) (Sig : List (Part D.naut.CG)) : Prop :=
  Formalism.MainNotions.N.HasParamW D.nd D.naut a σ Sig ∧ (D.nd.goodRow σ → ∀ p ∈ Sig, D.naut.csd p.π ∧ D.naut.ralg p.π)

def rowSig (D : D7) (a : D.nd.Loc) (σ : D.what₂.FT) : List (Part D.naut.CG) :=
  Classical.epsilon (IsRowPar D a σ)

theorem rowSig_isRowPar (D : D7) (hP : RowPar D) (a : D.nd.Loc) (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j a) σ ≠ ⊥) :
    IsRowPar D a σ (rowSig D a σ) :=
  Classical.epsilon_spec (hP a σ hσ)

theorem rowSig_spec (D : D7) (hP : RowPar D) (a : D.nd.Loc) (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j a) σ ≠ ⊥) :
    Formalism.MainNotions.N.HasParamW D.nd D.naut a σ (rowSig D a σ) :=
  (rowSig_isRowPar D hP a σ hσ).1

theorem rowSig_csd_ralg (D : D7) (hP : RowPar D) (a : D.nd.Loc) (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j a) σ ≠ ⊥)
    (hg : D.nd.goodRow σ) (π : D.naut.CG D.R.r) (hS : rowSig D a σ = [⟨D.R.r, π, 1⟩]) : D.naut.csd π ∧ D.naut.ralg π :=
  (rowSig_isRowPar D hP a σ hσ).2 hg ⟨D.R.r, π, 1⟩ (by rw [hS]; exact List.mem_singleton_self _)

def rowRho (D : D7) (hG : GalRepEx D) (a : D.nd.Loc) (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) :
    Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar (D.nd.l a)) :=
  Classical.choose (hG a D.R.r (one_le_r D) π hc hr)

theorem rowRho_spec (D : D7) (hG : GalRepEx D) (a : D.nd.Loc) (π : D.naut.CG D.R.r) (hc : D.naut.csd π)
    (hr : D.naut.ralg π) : IsRepOfSigQ D a D.R.r [⟨D.R.r, π, 1⟩] (rowRho D hG a π hc hr) :=
  Classical.choose_spec (hG a D.R.r (one_le_r D) π hc hr)

def etaChar (D : D7) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D) (a : D.nd.Loc) : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (Qbar (D.nd.l a))ˣ :=
  Matrix.GeneralLinearGroup.det.comp (Classical.choose (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη))

def rhoOfRow (D : D7) (hG : GalRepEx D) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D) (a : D.nd.Loc)
    (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) :
    Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar (D.nd.l a)) :=
  twistRep (rowRho D hG a π hc hr) (etaChar D hC hη a)

end Formalism.L2.NR
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual NumberField IsDedekindDomain Polynomial
open scoped Pointwise

namespace Formalism.L2.NR

structure NRhoTied (D : D7) : Prop where
  rbarSS : ∀ (σ : D.what₂.FT) (lam : D.what₂.places.Pl), (∃ a : D.nd.Loc, D.nd.w a = lam) →
    Formalism.MainNotions.N.IsSSRep (D.ntypes.rbar σ lam)
  rbar : ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
    ∀ (Sig : List (Part D.naut.CG)) (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)),
      Formalism.MainNotions.N.HasParamW D.nd D.naut i σ Sig → Formalism.MainNotions.N.IsRepOfSig D.nd D.naut i Sig ρ →
      ∀ g, (((D.ntypes.rbar σ (D.nd.w i) g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).map
          (Formalism.MainNotions.N.fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom =
        ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
          ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i)))
  rhoS : ∀ (hP : RowPar D) (hG : GalRepEx D) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D)
    (a : D.nd.Loc) (s : D.ntw.Sig (D.ntw.twOf a)), D.ntw.side _ s = D.ntw.twSide a → D.ntw.jS _ s = D.nd.j a →
    ∃ (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j a) σ ≠ ⊥) (hg : D.nd.goodRow σ),
      ∀ (π : D.naut.CG D.R.r) (hS : rowSig D a σ = [⟨D.R.r, π, 1⟩]),
        IsConjRep (Formalism.MainNotions.N.mapRep ((Formalism.MainNotions.N.iotaOQ D.nd D.naut a).comp (D.ntw.twist₂ a)) (D.ntw.rhoS _ s))
          (rhoOfRow D hG hC hη a π (rowSig_csd_ralg D hP a σ hσ hg π hS).1 (rowSig_csd_ralg D hP a σ hσ hg π hS).2)

section transport

variable {E Ω L : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [Field L] [NumberField L]

theorem val_le_one_of_isIntegral (B : ValuationSubring Ω) {y : Ω} (hy : IsIntegral ℤ y) : B.valuation y ≤ 1 :=
  (Valuation.valuationSubring.integers B.valuation).isIntegral_iff_v_le_one.mp (IsIntegral.tower_top hy)

theorem val_k_le_one (k : AlgebraicClosure L ≃+* Ω) (B : ValuationSubring Ω) (x : 𝓞 (AlgebraicClosure L)) :
    B.valuation (k (x : AlgebraicClosure L)) ≤ 1 := by
  apply val_le_one_of_isIntegral
  have hx : IsIntegral ℤ (x : AlgebraicClosure L) := x.2
  exact hx.map (k.toRingHom.toIntAlgHom)

def intoB (k : AlgebraicClosure L ≃+* Ω) (B : ValuationSubring Ω) : 𝓞 (AlgebraicClosure L) →+* B :=
  (k.toRingHom.comp (algebraMap (𝓞 (AlgebraicClosure L)) (AlgebraicClosure L))).codRestrict B
    (fun x => (B.valuation_le_one_iff _).mp (val_k_le_one k B x))

def primeOf (k : AlgebraicClosure L ≃+* Ω) (B : ValuationSubring Ω) : Ideal (𝓞 (AlgebraicClosure L)) :=
  (IsLocalRing.maximalIdeal B).comap (intoB k B)

instance primeOf_isPrime (k : AlgebraicClosure L ≃+* Ω) (B : ValuationSubring Ω) : (primeOf k B).IsPrime :=
  Ideal.comap_isPrime _ _

theorem normV_eq_absNorm (j : E ≃+* L) (w : HeightOneSpectrum (𝓞 E)) :
    normV w = Ideal.absNorm (mapPl j w).asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, normV]
  refine Nat.card_congr (Ideal.quotientEquiv w.asIdeal (mapPl j w).asIdeal (RingOfIntegers.mapRingEquiv j) ?_).toEquiv
  ext y
  rw [Ideal.map_comap_of_equiv, Ideal.mem_comap]
  obtain ⟨x, rfl⟩ := (RingOfIntegers.mapRingEquiv j).surjective y
  rw [mem_mapPl]
  simp

end transport

section charpolyInv

variable {K : Type} [Field K]

theorem reverse_X_sub_C (μ : K) : (X - C μ : K[X]).reverse = 1 - C μ * X := by
  have h1 : (1 : K[X]).reverse = 1 := by simp only [reverse, natDegree_one, reflect_one, pow_zero]
  have hX : (X : K[X]).reverse = 1 := by simpa [h1] using reverse_X_mul (1 : K[X])
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, C_neg, neg_mul, ← sub_eq_add_neg]

theorem reverse_prod_X_sub_C (s : Multiset K) :
    (s.map fun μ => X - C μ).prod.reverse = (s.map fun μ => 1 - C μ * X).prod := by
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.map_zero, Multiset.prod_zero, reverse, natDegree_one, reflect_one, pow_zero]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, ih, reverse_X_sub_C, Multiset.map_cons,
      Multiset.prod_cons]

theorem one_sub_C_mul_X (μ : K) (h : μ ≠ 0) : (1 - C μ * X : K[X]) = C (-μ) * (X - C μ⁻¹) := by
  rw [C_neg, neg_mul, mul_sub, ← C_mul, mul_inv_cancel₀ h, C_1]
  ring

theorem charpoly_inv_of_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : IsUnit M) (s : Multiset K)
    (hs : M.charpoly = (s.map fun μ => X - C μ).prod) :
    (M⁻¹).charpoly = (s.map fun μ => X - C μ⁻¹).prod := by
  have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).mp hM).ne_zero
  set c : K := (s.map fun μ => -μ).prod with hc
  have hcoeff : M.charpoly.coeff 0 = c := by
    rw [hs, coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map, hc]
    congr 1
    apply Multiset.map_congr rfl
    intro μ _
    simp
  have hdetc : M.det = (-1) ^ n * c := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hcoeff, Fintype.card_fin]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdetc
    exact hdet hdetc
  have hμ : ∀ μ ∈ s, μ ≠ 0 := by
    intro μ hμ h0
    apply hc0
    rw [hc]
    apply Multiset.prod_eq_zero
    rw [Multiset.mem_map]
    exact ⟨μ, hμ, by rw [h0, neg_zero]⟩
  have hrev : M.charpolyRev = C c * (s.map fun μ => X - C μ⁻¹).prod := by
    rw [← Matrix.reverse_charpoly, hs, reverse_prod_X_sub_C]
    rw [Multiset.map_congr rfl (fun μ hm => one_sub_C_mul_X μ (hμ μ hm)), Multiset.prod_map_mul, hc]
    congr 1
    rw [map_multiset_prod, Multiset.map_map]
    rfl
  rw [Matrix.charpoly_inv M hM, hrev, Ring.inverse_eq_inv, hdetc, Fintype.card_fin]
  have hpm : ((-1 : K) ^ n) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hscal : (-1 : K) ^ n * ((-1 : K) ^ n * c)⁻¹ * c = 1 := by
    rw [mul_inv, show (-1 : K) ^ n * (((-1 : K) ^ n)⁻¹ * c⁻¹) * c = ((-1 : K) ^ n * ((-1 : K) ^ n)⁻¹) * (c⁻¹ * c) by ring,
      mul_inv_cancel₀ hpm, inv_mul_cancel₀ hc0, one_mul]
  have key : (-1 : K[X]) ^ n * C (((-1 : K) ^ n * c)⁻¹) * (C c * (s.map fun μ => X - C μ⁻¹).prod) =
      C ((-1 : K) ^ n * ((-1 : K) ^ n * c)⁻¹ * c) * (s.map fun μ => X - C μ⁻¹).prod := by
    rw [map_mul, map_mul, map_pow, map_neg, C_1]
    ring
  rw [key, hscal, C_1, one_mul]

theorem charpoly_GL_inv {n : ℕ} (g : GL (Fin n) K) (s : Multiset K)
    (hs : (g : Matrix (Fin n) (Fin n) K).charpoly = (s.map fun μ => X - C μ).prod) :
    ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly = (s.map fun μ => X - C μ⁻¹).prod := by
  rw [Matrix.coe_units_inv]
  exact charpoly_inv_of_eq _ (Units.isUnit g) s hs

theorem charpoly_map_of_inv {L : Type} [Field L] {n : ℕ} (f : K →+* L) (g : GL (Fin n) K) (s : Multiset L)
    (hs : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.map f = (s.map fun μ => X - C μ).prod) :
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.map f = (s.map fun μ => X - C μ⁻¹).prod := by
  let g' : GL (Fin n) L := Units.map (f.mapMatrix : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) L).toMonoidHom g
  have hg : g'⁻¹ = Units.map (f.mapMatrix : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) L).toMonoidHom g⁻¹ :=
    (map_inv _ g).symm
  have h1 : ((g'⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).charpoly = (s.map fun μ => X - C μ).prod := by
    rw [hg, Units.coe_map]
    show (f.mapMatrix ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).charpoly = _
    rw [RingHom.mapMatrix_apply, Matrix.charpoly_map, hs]
  have h2 := charpoly_GL_inv g'⁻¹ s h1
  rw [inv_inv] at h2
  rw [← h2, ← Matrix.charpoly_map]
  rfl

end charpolyInv

section norm

end norm

section ss

variable {Γ : Type} [Group Γ] {K : Type} [Field K] {n : ℕ}

end ss

section krull

variable {E Ω L : Type} [Field E] [Field Ω] [Algebra E Ω] [Field L]

end krull

section transfer

variable {E Ω L : Type} [Field E] [Field Ω] [Algebra E Ω] [Field L]
variable {K : Type} [Field K] [TopologicalSpace K] {a b : ℕ}

end transfer

section gal

variable (D : D7) (T : NormalizedHeckeDataPlaceholder D)

end gal

theorem exists_frame {E Ω L : Type} [Field E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Field L] (j : E ≃+* L) :
    ∃ k : AlgebraicClosure L ≃+* Ω, FrameOver j k :=
  ⟨IsAlgClosure.equivOfEquiv (AlgebraicClosure L) Ω j.symm, fun x => by
    rw [IsAlgClosure.equivOfEquiv_algebraMap, RingEquiv.symm_apply_apply]⟩

theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) : (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem isoLoc_single (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    Formalism.MainNotions.N.isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [Formalism.MainNotions.N.isoLoc, Formalism.MainNotions.N.spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

end Formalism.L2.NR
end
end
