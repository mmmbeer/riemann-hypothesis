import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt

attribute [local instance] Over.cartesianMonoidalCategory

example : @JetR = @ReciprocityTheory.ChartRestriction.G.Chart.JetR := rfl
example : @zR = @ReciprocityTheory.ChartRestriction.G.Chart.zR := rfl

def NilSt : Prop :=
  ∀ (p : ℕ), p ≠ 0 → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C], v.Integers O → ∀ [IsLocalRing O], ¬ IsUnit (p : O) →
    ∀ c ∈ maximalIdeal O, ∀ n : ℕ, ∃ N : ℕ, c ^ N ∈ Ideal.span {(p : O) ^ n}

def JetSt : Prop :=
  ∀ (T B : Type) [CommRing T] [CommRing B] [Algebra T B] (κ : Type) [Finite κ] (b : κ → B),
    (∀ j, IsNilpotent (b j)) → ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∃! ψ : JetR T κ k →ₐ[T] B, ∀ j, ψ (zR k j) = b j

def EvalSt : Prop :=
  ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O] (I : Ideal O) (m d k : ℕ)
    (χ : JetR T (Fin m × Fin d) k →ₐ[T] O ⧸ I) (c : Fin m → Fin d → O),
    (∀ q, χ (zR k q) = Ideal.Quotient.mk I (c q.1 q.2)) → ∀ f : PS T m d,
      χ (psJet k f) = Ideal.Quotient.mk I (MvPolynomial.eval (fun q : Fin m × Fin d => c q.1 q.2)
        (MvPowerSeries.trunc O (Finsupp.equivFunOnFinite.symm fun _ => k + 1) (MvPowerSeries.map (algebraMap T O) f)))

def SepSt : Prop :=
  ∀ (T A O : Type) [CommRing T] [CommRing A] [Algebra T A] [CommRing O] [Algebra T O] (p : O),
    IsHausdorff (Ideal.span {p}) O → ∀ h h' : A →ₐ[T] O,
      (∀ n : ℕ, (Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).comp h = (Ideal.Quotient.mkₐ T _).comp h') → h = h'

def AlgLimSt : Prop :=
  ∀ (T A O : Type) [CommRing T] [CommRing A] [Algebra T A] [CommRing O] [Algebra T O] (p : O),
    IsAdicComplete (Ideal.span {p}) O → ∀ a : ∀ n : ℕ, A →ₐ[T] O ⧸ Ideal.span {p ^ n},
      (∀ (n : ℕ) (z : A) (y : O), Ideal.Quotient.mk _ y = a (n + 1) z → Ideal.Quotient.mk _ y = a n z) →
      ∃ h : A →ₐ[T] O, ∀ n, (Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).comp h = a n

end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
end
end

section
set_option autoImplicit false

noncomputable section

open IsLocalRing MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.Chart (jetLift jetLift_zR jet_ext)

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt




theorem smod_iff {O : Type} [CommRing O] (p : O) (n : ℕ) (u w : O) :
    u ≡ w [SMOD ((Ideal.span {p}) ^ n • ⊤ : Submodule O O)] ↔
      Ideal.Quotient.mk (Ideal.span {p ^ n}) u = Ideal.Quotient.mk _ w := by
  have h : ((Ideal.span {p}) ^ n • ⊤ : Submodule O O) = Ideal.span {p ^ n} := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  rw [SModEq.sub_mem, Ideal.Quotient.eq, h]

theorem eq_of_mod {O : Type} [CommRing O] (p : O) (hH : IsHausdorff (Ideal.span {p}) O) (u w : O)
    (h : ∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {p ^ n}) u = Ideal.Quotient.mk _ w) : u = w := by
  refine sub_eq_zero.mp (hH.haus (u - w) fun n => (smod_iff p n (u - w) 0).mpr ?_)
  rw [map_sub, map_zero, h n, sub_self]

theorem sepSt : SepSt := by
  intro T A O _ _ _ _ _ p hH h h' H
  ext z
  refine eq_of_mod p hH (h z) (h' z) fun n => ?_
  have := AlgHom.congr_fun (H n) z
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using this

theorem algLimSt : AlgLimSt := by
  intro T A O _ _ _ _ _ p hC a hc
  have hdown : ∀ z : A, ∀ m n : ℕ, m ≤ n → ∀ y : O,
      Ideal.Quotient.mk (Ideal.span {p ^ n}) y = a n z →
        Ideal.Quotient.mk (Ideal.span {p ^ m}) y = a m z := by
    intro z m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact fun y hy => hy
    | succ n _ ih => exact fun y hy => ih y (hc n z y hy)
  have hlim : ∀ z : A, ∃ L : O, ∀ n, Ideal.Quotient.mk (Ideal.span {p ^ n}) L = a n z := by
    intro z
    have hs : ∀ n, ∃ y : O, Ideal.Quotient.mk (Ideal.span {p ^ n}) y = a n z :=
      fun n => Ideal.Quotient.mk_surjective (a n z)
    choose y hy using hs
    obtain ⟨L, hL⟩ := hC.toIsPrecomplete.prec' y (fun {m n} hmn =>
      (smod_iff p m (y m) (y n)).mpr (by rw [hy m, hdown z m n hmn (y n) (hy n)]))
    exact ⟨L, fun n => by rw [← (smod_iff p n (y n) L).mp (hL n), hy n]⟩
  choose L hL using hlim
  have huniq : ∀ x y : O, (∀ n : ℕ, Ideal.Quotient.mk (Ideal.span {p ^ n}) x =
      Ideal.Quotient.mk (Ideal.span {p ^ n}) y) → x = y :=
    fun x y H => eq_of_mod p hC.toIsHausdorff x y H
  refine ⟨
    { toFun := L
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }, ?_⟩
  · exact huniq _ _ fun n => by simp only [hL, map_one]
  · intro x y
    exact huniq _ _ fun n => by simp only [hL, map_mul]
  · exact huniq _ _ fun n => by simp only [hL, map_zero]
  · intro x y
    exact huniq _ _ fun n => by simp only [hL, map_add]
  · intro t
    refine huniq _ _ fun n => ?_
    rw [hL, AlgHom.commutes]
    exact ((Ideal.Quotient.mkₐ T (Ideal.span {p ^ n})).commutes t).symm
  · intro n
    ext z
    exact hL z n

end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
end
end
