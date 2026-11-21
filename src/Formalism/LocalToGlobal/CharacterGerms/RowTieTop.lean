import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.DualLattices.U10
import Formalism.SharpRestriction.GrowthBounds.FittingIdeal.DetMulMemFitt0

section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace ValuationFitting

open ReciprocityTheory.PGsh.Up CharacteristicFromRanks

variable {C : Type} [Field C]

instance factL (V : VF C) : Fact V.l.Prime := ⟨V.l_prime⟩

def ValTie (V : VF C) (vm : Valuation C NNReal) : Prop :=
  ∀ x : C, x ≠ 0 → ∃ t : ℝ, V.v x = (t : WithTop ℝ) ∧ (vm x : ℝ) = (vm (V.l : C) : ℝ) ^ t

structure Comparison₂ {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    (G : ∀ g, Cart V d (I g) (J g)) (big : Fin 2 → ZMod d → Prop) (rh : ℕ) (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    (O : Type) [CommRing O] [Algebra ℤ_[V.l] O] (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (H : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp H) where
  val : ValTie V vm
  ix : Fin 2 → ZMod d → Fin U.m
  ix_frob : ∀ g a, U.φ (ix g a) = ix g (a + 1)
  ix_conj : ∀ g a, U.cj (ix g a) = ix (1 - g) a
  rank : ∀ g a, U.r (ix g a) + rh = pT G g a
  e : ∀ g a, Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a}
  αR : ∀ g a, Matrix (Fin (pT G g a)) (Fin (h g)) R
  αR_eq : ∀ g a c i, algebraMap R C (αR g a c i) = ht g i (e g a c)
  bad : ∀ g a, big g a → Nonempty (cokE H.Ht U.εT U.εL (ix g a) (U.cj (ix g a)) ≃ₗ[R]
    ((Fin (pT G g a) → R) ⧸ LinearMap.range (αR g a).mulVecLin))

def FittGe : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (m h : ℕ) (α : Matrix (Fin m) (Fin h) R) (x : NNReal),
    HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x →
    ∃ y ∈ S4.fitt0 α, v (algebraMap R C y) = x

section Val

variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

def vA (V : VF C) (R : Type) [CommRing R] [Algebra R C] : AddValuation R (WithTop ℝ) :=
  V.v.comap (algebraMap R C)

theorem vA_apply (x : R) : vA V R x = V.v (algebraMap R C x) := rfl

theorem vA_nonneg (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) : ∀ x : R, 0 ≤ vA V R x := by
  intro x
  rw [vA_apply]
  by_cases hx : algebraMap R C x = 0
  · rw [hx, V.v.map_zero]; exact le_top
  · obtain ⟨t, ht1, ht2⟩ := hT _ hx
    rw [ht1]
    have hle : (vm (algebraMap R C x) : ℝ) ≤ 1 := by exact_mod_cast hv.map_le_one x
    have : 0 ≤ t := by
      by_contra hneg
      have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (not_le.mp hneg)
      rw [← ht2] at this
      linarith
    exact_mod_cast this

theorem lenCoker_vA {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) :
    S4.lenCoker (vA V R) α = S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) := by
  unfold S4.lenCoker
  congr 1
  funext g
  rw [vA_apply, RingHom.map_det]
  rfl

end Val


theorem rpow_neg_succ {l : ℕ} (hl : 0 < l) (n : ℕ) :
    (l : ℝ) ^ (-((n : ℝ) + 1)) = ((l : ℝ) ^ (n + 1))⁻¹ := by
  have h0 : (0 : ℝ) ≤ l := by positivity
  rw [Real.rpow_neg h0, ← Nat.cast_succ, Real.rpow_natCast]





section Val2

variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem lenCoker_eq_logb (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : HasLen vm R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) (hpos : 0 < (x : ℝ)) :
    S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) =
      ((Real.logb (vm (V.l : C) : ℝ) x : ℝ) : WithTop ℝ) := by
  have hxb : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x = x :=
    Real.rpow_logb h0 (ne_of_lt h1) hpos
  rw [← lenCoker_vA]
  apply le_antisymm
  · obtain ⟨y, hy, hyV⟩ := Formalism.MainNotions.G.ValuationFitting.fitt_ge hv α hx
    have hy0 : algebraMap R C y ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hyV
      rw [← hyV] at hpos
      simp at hpos
    obtain ⟨t, ht1, ht2⟩ := hT _ hy0
    refine le_trans (S4.lenCoker_le_of_mem (vA V R) (vA_nonneg hT hv h0 h1) _ hy) ?_
    rw [vA_apply, ht1]
    have : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x ≤ (vm (V.l : C) : ℝ) ^ t := by
      rw [hxb, ← ht2, hyV]
    rw [Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at this
    exact_mod_cast this
  · unfold S4.lenCoker
    refine Finset.le_inf fun g _ => ?_
    rw [vA_apply]
    by_cases hz : algebraMap R C (α.submatrix id g).det = 0
    · rw [hz, V.v.map_zero]; exact le_top
    · obtain ⟨t, ht1, ht2⟩ := hT _ hz
      rw [ht1]
      have hle : (vm (algebraMap R C (α.submatrix id g).det) : ℝ) ≤ x := by
        exact_mod_cast Formalism.MainNotions.G.ValuationFitting.fitt_le hv α hx g
      rw [ht2, ← hxb, Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at hle
      exact_mod_cast hle

end Val2




end ValuationFitting

end Formalism.L2.FormalSeriesBounds
end
end

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem card_sigma_fst {d : ℕ} [NeZero d] (m : ZMod d → ℕ) (a : ZMod d) :
    (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a).card = m a := by
  rw [show (Finset.univ.filter fun x : (Σ a : ZMod d, Fin (m a)) => x.1 = a) =
      (Finset.univ : Finset (Fin (m a))).map ⟨Sigma.mk a, sigma_mk_injective⟩ from ?_]
  · simp
  · ext x
    obtain ⟨b, i⟩ := x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨i, rfl⟩
    · rintro ⟨j, hj⟩
      exact (congrArg Sigma.fst hj).symm

section CH

open ReciprocityTheory.PGsh.Up CharacteristicFromRanks ValuationFitting

variable {C : Type} [Field C]

end CH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}

section Rank

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

theorem rankHyp_ofLab {C3 : IntChart T io y} {ι : T.Fr →+* C} {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.raw (pairOfLab ha hg o)).RankHyp where
  big_compl := (hr o).1
  rk_big := fun g a hb => (card_sigma_fst (fun a => Dw.mult (lab.tau o g a)) a).trans ((hr o).2.1 g a hb)
  rk_small := fun g a hb => (card_sigma_fst (fun a => Dw.mult (lab.tau o g a)) a).trans ((hr o).2.2 g a hb)

end Rank

section Named

variable (Xo c)

def AllCharts (Φ : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (dd : ℕ),
    RawChart C d I (Fin dd) → Prop) : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, Φ C V d (lab.II Dw o) (chD C3.ch) (Y.raw (pairOfLab ha hg o))

def RankMaximalCharts : Prop := AllCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition Hc

def CharacterHypothesisAllCharts : Prop := AllCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.CHSt Hc

end Named

section Top

variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} {d : ℕ} [NeZero d]

theorem hypotheses_of_labelling (hCart : CartFBSt) (hAx : AxesFBSt) (hG0 : IntegralGermIndependentAllCharts) (hC : CEqFBSt) (hR1 : IndependenceBoundAllCharts)
    (hR2 : RankMaximalCharts Xo c) (hCH : CharacterHypothesisAllCharts Xo c) (hstar : ∀ a : 𝓞 E, star a = H.bar a)
    {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι) {k : ℕ}
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ι k Y) {lab : Lab E Orb d}
    (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab) (hr : lab.RankOK Dw) (o : Orb) :
    (Y.raw (pairOfLab ha hg o)).Hyps V :=
  FBChart.hyps hCart hAx hG0 hC hR1 Y (pairOfLab ha hg o) (rankHyp_ofLab ha hg hr o)
    (hR2 hstar _ _ _ C3 C V ι hι k Y hY Orb d lab ha hg hr o _)
    (hCH hstar _ _ _ C3 C V ι hι k Y hY Orb d lab ha hg hr o _)

end Top

end Formalism.L2.FormalSeriesBounds
end
end
