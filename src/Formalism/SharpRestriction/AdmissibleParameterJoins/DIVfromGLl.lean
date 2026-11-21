import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLk
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes

section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw

theorem mEatT_nat (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ∃ n : ℕ, (D.R.m : ℝ) * EatT D u w = n := by
  classical
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨b, hb⟩ := D.R.t_odd
  have hm : (D.R.m : ℝ) = 2 * (a : ℝ) := by rw [ha]; push_cast; ring
  have ht : (D.R.t : ℝ) = 2 * (b : ℝ) + 1 := by rw [hb]; push_cast; ring
  unfold EatT
  split_ifs with hs
  · first
    | simp only [Formalism.MainNotions.G.Nm]
    | simp only [Formalism.Nm]
    | skip
    refine ⟨D.R.m * (2 * ∑ τ : D.what₂.Tau, Wtau D u τ) + D.R.m * D.R.f * D.R.N D.R.m +
      (topsOf D.host D.eTau).card * (b + 1) * a * (2 * a + 1), ?_⟩
    push_cast
    rw [hm, ht]
    ring
  · exact ⟨0, by simp⟩

theorem vAdd_Tpow (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hw : D.what₂.places.resChar w = (D.mem u).A.T) (n : ℕ) :
    D.what₂.places.val w ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n) = (((n * D.what₂.places.ramIdx w : ℕ) : ℤ) : WithTop ℤ) := by
  rw [AddValuation.map_pow, ← hw, D.what₂.places.val_resChar w, ← WithTop.coe_nsmul]
  congr 1

theorem ColGe0_atT (D : D7) (u : D.what₂.Word) (h5 : Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u) (w : D.what₂.places.Pl)
    (hw : D.what₂.places.resChar w = (D.mem u).A.T) (x : ((D.fm u).lat 0).V) (hx : x ∈ LT.Nlam D u w) :
    ColGe0 D u w x (-((D.R.m : ℝ) * EatT D u w)) := by
  obtain ⟨n0, hn0⟩ := mEatT_nat D u w
  have hT0 : (((D.mem u).A.T : ℕ) : D.what₂.LL) ≠ 0 := by
    have hp := D.what₂.places.resChar_prime w
    rw [hw] at hp
    exact_mod_cast hp.ne_zero
  have hc0 : (((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0 ≠ 0 := pow_ne_zero _ hT0
  have hval := vAdd_Tpow D u w hw n0
  have hle : (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * Formalism.MainNotions.product_first_zeroth_parts.ET D u w) ≤
      (((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) : ℝ) := by
    show (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * EatT D u w) ≤ _
    rw [hn0]
    push_cast
    rw [mul_comm]
  obtain ⟨y', hy'S, hy'⟩ := h5 w hw _ _ hval hle x hx
  refine ⟨((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ • y', ?_,
    ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹, y', hy'S, rfl, Or.inr ?_⟩
  · rw [map_smulₛₗ, hy', smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
    rfl
  · have hinv : D.what₂.places.val w ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ =
        ((-((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
      rw [AddValuation.map_inv, hval]
      rfl
    have hv := D.val_eq w _ (inv_ne_zero hc0)
    rw [hinv] at hv
    have hvz : vAdd (D.plEq w) ((((D.mem u).A.T : ℕ) : D.what₂.LL) ^ n0)⁻¹ =
        -((n0 * D.what₂.places.ramIdx w : ℕ) : ℤ) := (WithTop.coe_injective hv).symm
    rw [hvz]
    show (D.what₂.places.ramIdx w : ℝ) * (-((D.R.m : ℝ) * EatT D u w)) ≤ _
    rw [hn0]
    push_cast
    nlinarith

end Formalism.MainNotions.J

end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

def Per0 (D : D7) : Prop :=
  DGamDef D → ∀ u, ∀ x ∈ (D.fm u).ptLat.L, ∀ F ∈ (D.what₂.Mtilde D.what₂.mu0).carrier, F ∈ D.what₂.V0 D.what₂.mu0 →
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.mem u).P.period ((D.fm u).ptEmb x) ((D.eMt u).symm F) ∧
      ∀ w : D.what₂.places.Pl, y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)

def PerTw (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  DGamDef D → ∀ u μ, μ ≠ D.what₂.mu0 → ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
    ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).period ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Dx.Qp μ →
        y = 0 ∨ -ur D w (vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ)

def PtTw (D : D7) (T : TwForms D) : Prop :=
  ∀ u μ, μ ≠ D.what₂.mu0 → ∃ h : (T.fm u μ).PRat, (T.fm u μ).PtilIntegral h

def PeriodBoundAtLevelPrime (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ φ : (D.div.Nu u).V, φ ∈ L.NuLat u →
    ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier, F ∈ D.what₂.V0 (D.what₂.muAt w) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u (D.what₂.muAt w) (D.jN u φ) F ∧
        (y = 0 ∨ ur D w (L.sg u w) ≤ (vAdd (D.plEq w) y : ℝ))


theorem pair_loc (D : D7) (w : D.what₂.places.Pl) (k : ℤ) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (NumberField.RingOfIntegers D.what₂.LL) V] (Λ : Submodule (NumberField.RingOfIntegers D.what₂.LL) V) (l : V → ℂ)
    (h0 : l 0 = 0) (hadd : ∀ x y, l (x + y) = l x + l y) (hsm : ∀ (a : D.what₂.LL) x, l (a • x) = D.what₂.embLL a * l x)
    (h : ∀ x ∈ Λ, ∃ y : D.what₂.LL, D.what₂.embLL y = l x ∧ ((k : ℤ) : WithTop ℤ) ≤ D.what₂.places.val w y) :
    ∀ z ∈ locW D.what₂.places w Λ, ∃ y : D.what₂.LL, D.what₂.embLL y = l z ∧ ((k : ℤ) : WithTop ℤ) ≤ D.what₂.places.val w y := by
  intro z hz
  unfold locW at hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, by rw [map_zero, h0], by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hav⟩ := hx
    obtain ⟨b, hb, hbv⟩ := hy
    refine ⟨a + b, by rw [map_add, ha, hb, hadd], ?_⟩
    exact le_trans (le_min hav hbv) (AddValuation.map_add _ _ _)
  | smul c x _ hx =>
    obtain ⟨a, ha, hav⟩ := hx
    refine ⟨(c : D.what₂.LL) * a, ?_, ?_⟩
    · rw [map_mul, ha]
      exact (hsm (c : D.what₂.LL) x).symm
    · rw [AddValuation.map_mul]
      have hc : (0 : WithTop ℤ) ≤ D.what₂.places.val w (c : D.what₂.LL) := c.2
      calc ((k : ℤ) : WithTop ℤ) = 0 + ((k : ℤ) : WithTop ℤ) := (zero_add _).symm
        _ ≤ _ := add_le_add hc hav




def LevelPrimeColumnOtherTuples (D : D7) (Dx : DivX D) (T : TwForms D) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ μ, μ ≠ D.what₂.mu0 → D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam D u w,
      ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w))

end Formalism.MainNotions.J

end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}





theorem sizeData_at_level_primes_of_defs {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef) (hE : L.EDef X K c)
    (hTg : LevelPrimeNotTypePrime D) : LevelPrimeSizes D L := ETDef_of P hF hE hTg

end Formalism.MainNotions.J

end
end
