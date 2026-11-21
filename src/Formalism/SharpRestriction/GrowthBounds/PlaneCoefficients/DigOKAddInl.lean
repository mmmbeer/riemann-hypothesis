import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.NoOpStep
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TwistSubXMemSupported

section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

section Gen

variable {σ R : Type*} [CommRing R]

theorem X_mul_mono (v : σ) (mo : σ →₀ ℕ) (c : R) : X v * monomial mo c = monomial (mo + Finsupp.single v 1) c := by
  rw [X, monomial_mul, one_mul, add_comm]


theorem pderiv_add_single (w : σ) (L : σ →₀ ℕ) (c : R) :
    pderiv w (monomial (L + Finsupp.single w 1) c) = monomial L (c * ((L w : R) + 1)) := by
  rw [pderiv_monomial, add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same]
  push_cast
  rfl

theorem pderiv_mono_zero (w : σ) (L : σ →₀ ℕ) (c : R) (h : L w = 0) : pderiv w (monomial L c) = 0 := by
  rw [pderiv_monomial, h, Nat.cast_zero, mul_zero, map_zero]

theorem exists_add_single (w : σ) (L : σ →₀ ℕ) (h : L w ≠ 0) : ∃ L', L = L' + Finsupp.single w 1 := ⟨L - Finsupp.single w 1,
  (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))).symm⟩

end Gen

theorem stepB {P e : ℕ} (hP : 0 < P) (h : e % P + 1 = P) : (e + 1) % P = 0 ∧ (e + 1) / P = e / P + 1 := by
  obtain ⟨h1, h2⟩ := (Nat.div_mod_unique (a := e + 1) (d := e / P + 1) (c := 0) hP).mpr
    ⟨by rw [mul_add, mul_one]; have := Nat.mod_add_div e P; linarith, hP⟩
  exact ⟨h2, h1⟩

section PolS

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ}

theorem multideg_add_single (mo : ι × Fin n →₀ ℕ) (x0 : ι) (a : Fin n) (i : ι) :
    multideg (mo + Finsupp.single (x0, a) 1) i = multideg mo i + if i = x0 then 1 else 0 := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  congr 1
  by_cases h : i = x0
  · subst h
    simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, h, Ne.symm h]

theorem mem_Pol' {d : ι → ℕ} {F : MvPolynomial (ι × Fin n) R} :
    F ∈ Pol R n d ↔ ∀ m ∈ F.support, ∀ i, multideg m i = d i := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  constructor
  · intro h m hm
    exact h hm
  · intro h m hm
    exact h m hm

theorem mono_mem_Pol {d : ι → ℕ} (m : ι × Fin n →₀ ℕ) (c : R) (h : ∀ i, multideg m i = d i) :
    monomial m c ∈ Pol R n d := by
  rw [mem_Pol']
  intro m' hm'
  have h1 := support_monomial_subset hm'
  rw [Finset.mem_singleton] at h1
  rw [h1]
  exact h

theorem Pol_pderiv {d d' : ι → ℕ} (x0 : ι) (a : Fin n) (h0 : d' x0 = d x0 + 1) (h1 : ∀ i, i ≠ x0 → d' i = d i)
    {H : MvPolynomial (ι × Fin n) R} (hH : H ∈ Pol R n d') : pderiv (x0, a) H ∈ Pol R n d := by
  rw [mem_Pol'] at hH
  rw [H.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  by_cases hz : m (x0, a) = 0
  · rw [pderiv_mono_zero _ _ _ hz]
    exact Submodule.zero_mem _
  · obtain ⟨m', rfl⟩ := exists_add_single _ m hz
    rw [pderiv_add_single]
    apply mono_mem_Pol
    intro i
    have hi := hH _ hm i
    rw [multideg_add_single] at hi
    by_cases hix : i = x0
    · subst hix
      simp at hi
      omega
    · simp [hix] at hi
      rw [hi, h1 i hix]

theorem Pol_X_mul {d d' : ι → ℕ} (x0 : ι) (a : Fin n) (h0 : d x0 = d' x0 + 1) (h1 : ∀ i, i ≠ x0 → d' i = d i)
    {H : MvPolynomial (ι × Fin n) R} (hH : H ∈ Pol R n d') : X (x0, a) * H ∈ Pol R n d := by
  rw [mem_Pol'] at hH
  rw [H.as_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [X_mul_mono]
  apply mono_mem_Pol
  intro i
  rw [multideg_add_single, hH m hm i]
  by_cases hix : i = x0
  · subst hix
    simp
    omega
  · simp [hix]
    exact h1 i hix

end PolS

theorem valuation_ge_of_le_add_one {x y : WithTop ℤ} {t t' : ℝ} (h : x ≤ y + ((1 : ℤ) : WithTop ℤ)) (hx : geZ x t') (ht : t + 1 ≤ t') :
    geZ y t := by
  intro k hk
  rw [hk] at h
  have h' : x ≤ ((k + 1 : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_add]
    exact h
  induction x using WithTop.recTopCoe with
  | top => simp at h'
  | coe k'' =>
    have h2 := hx k'' rfl
    have h3 : (k'' : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast WithTop.coe_le_coe.mp h'
    linarith

section ValOp

variable {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

theorem val_mul (G : MvPolynomial (ι × Fin n) Kf) (w : ι × Fin n) {t t' : ℝ} (h0 : t ≤ t')
    (h1 : w.1 ∈ S → LL.vec w.1 = false → t + 1 ≤ t') (hG : geZ (valS LL S G) t') : geZ (valS LL S (X w * G)) t := by
  have geZ_mono : ∀ {x y : WithTop ℤ} {s s' : ℝ}, x ≤ y → geZ x s' → s ≤ s' → geZ y s := by
    intro x y s s' hxy hx hss k hk
    rw [hk] at hxy
    induction x using WithTop.recTopCoe with
    | top => simp at hxy
    | coe k'' =>
      have h2 := hx k'' rfl
      have h3 : (k'' : ℝ) ≤ (k : ℝ) := by exact_mod_cast WithTop.coe_le_coe.mp hxy
      linarith
  by_cases hc : w.1 ∈ S ∧ LL.vec w.1 = false
  · exact valuation_ge_of_le_add_one (valS_X_mul (LL := LL) (S := S) G w) hG (h1 hc.1 hc.2)
  · have hv : w.1 ∈ S → LL.vec w.1 = true := fun hs =>
      by
        cases hb : LL.vec w.1
        · exact absurd ⟨hs, hb⟩ hc
        · rfl
    exact geZ_mono (valS_X_mul_of (LL := LL) (S := S) G w hv) hG h0

end ValOp

end Formalism.MainNotions.PairMembershipBlocks
end
end

section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)

def Pof : TL J Dt.nL r × Fin r → ℕ
  | (⟨_, Sum.inl _⟩, _) => 1
  | (⟨j, Sum.inr m⟩, _) => Dt.P j m

def keyOf : TL J Dt.nL r × Fin r → Option ((ZMod J × Fin r) × Fin r)
  | (⟨_, Sum.inl _⟩, _) => none
  | (⟨j, Sum.inr m⟩, a) => some ((j, m), a)

theorem liftExp_eq (mo : TL J Dt.nL r × Fin r →₀ ℕ) (v : TL J Dt.nL r × Fin r) :
    Dt.liftExp mo v = mo v / Pof Dt v := by
  rcases v with ⟨⟨j, l | m⟩, a⟩
  · exact (Nat.div_one _).symm
  · rfl

theorem liftVar_inj : Function.Injective Dt.liftVar := by
  rintro ⟨⟨j, l | m⟩, a⟩ ⟨⟨j', l' | m'⟩, a'⟩ h <;>
    simp only [SignedChainData.liftVar, Prod.mk.injEq, reduceCtorEq, ML.ll.injEq, ML.wc.injEq, false_and] at h
  · obtain ⟨⟨rfl, h1⟩, rfl⟩ := h
    cases h1
    rfl
  · obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl

def liftE (mo : TL J Dt.nL r × Fin r →₀ ℕ) : TL J Dt.nL r × Fin r →₀ ℕ :=
  Finsupp.onFinset mo.support (fun v => mo v / Pof Dt v) (by
    intro v hv
    rw [Finsupp.mem_support_iff]
    intro h0
    apply hv
    simp [h0])

theorem liftE_apply (mo : TL J Dt.nL r × Fin r →₀ ℕ) (v : TL J Dt.nL r × Fin r) :
    liftE Dt mo v = mo v / Pof Dt v := rfl

def liftMon (mo : TL J Dt.nL r × Fin r →₀ ℕ) : ML J Dt.nL r × Fin r →₀ ℕ :=
  Finsupp.mapDomain Dt.liftVar (liftE Dt mo)

theorem prod_lift (mo : TL J Dt.nL r × Fin r →₀ ℕ) :
    ∏ v ∈ mo.support, (X (Dt.liftVar v) : MvPolynomial (ML J Dt.nL r × Fin r) (KK O)) ^ Dt.liftExp mo v =
      monomial (liftMon Dt mo) 1 := by
  have hsub : (liftE Dt mo).support ⊆ mo.support := by
    intro v hv
    rw [Finsupp.mem_support_iff] at hv ⊢
    rw [liftE_apply] at hv
    intro h0
    apply hv
    simp [h0]
  rw [liftMon, MvPolynomial.monomial_eq, C_1, one_mul,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => pow_zero _)]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [liftE_apply, liftExp_eq]

theorem Fdig_mono (rho : (ZMod J × Fin r) × Fin r → ℕ) (mo : TL J Dt.nL r × Fin r →₀ ℕ) (c : KK O) :
    Dt.Fdig rho (monomial mo c) = if Dt.digOK rho mo then monomial (liftMon Dt mo) c else 0 := by
  unfold SignedChainData.Fdig
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [support_monomial, if_neg hc, Finset.filter_singleton]
    split_ifs with h
    · rw [Finset.sum_singleton, coeff_monomial, if_pos rfl, prod_lift, C_mul_monomial, mul_one]
    · simp

theorem liftMon_w (mo : TL J Dt.nL r × Fin r →₀ ℕ) (v : TL J Dt.nL r × Fin r) :
    liftMon Dt mo (Dt.liftVar v) = mo v / Pof Dt v := by
  rw [liftMon, Finsupp.mapDomain_apply (liftVar_inj Dt)]
  rfl

def Oth (ke : (ZMod J × Fin r) × Fin r) (rho : (ZMod J × Fin r) × Fin r → ℕ) (mo : TL J Dt.nL r × Fin r →₀ ℕ) : Prop :=
  ∀ (j : ZMod J) (m : Fin r) (a : Fin r), ((j, m), a) ≠ ke → mo (⟨j, Sum.inr m⟩, a) % Dt.P j m = rho ((j, m), a)

end Formalism.MainNotions.PairMembershipBlocks
end
end
