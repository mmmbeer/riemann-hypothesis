import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
import Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemmaDN0

section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount

open Module PowerSeries

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem length_ne_top_of_smul {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
    (x : O) (hx : x ≠ 0) (h : ∀ m : M, x • m = 0) : Module.length O M ≠ ⊤ := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O M
  have hI : ∀ i : Fin n, Ideal.span {x} ≤
      LinearMap.ker (LinearMap.toSpanSingleton O M (f (Pi.single i 1))) := by
    intro i
    rw [Ideal.span_le]
    rintro _ rfl
    simp [h]
  let g : (Fin n → O ⧸ Ideal.span {x}) →ₗ[O] M :=
    ∑ i, ((Ideal.span {x}).liftQ _ (hI i)) ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro m
    obtain ⟨v, rfl⟩ := hf m
    refine ⟨fun i => Submodule.Quotient.mk (v i), ?_⟩
    have hv : v = ∑ i, v i • Pi.single i (1 : O) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul]; rfl
  have h1 : Module.length O (O ⧸ Ideal.span {x}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hx))
  have h2 := Module.length_le_of_surjective g hg
  rw [Module.length_pi] at h2
  intro htop
  rw [htop, top_le_iff] at h2
  rcases WithTop.mul_eq_top_iff.mp h2 with h3 | h3
  · exact h1 h3.2
  · have := ENat.card_eq_top.mp h3.1
    exact not_finite (Fin n)

def satL {O R : Type} [CommRing O] [AddCommGroup R] [Module O R] (l : O) (R' : Submodule O R) : Submodule O R where
  carrier := {z | ∃ t : ℕ, l ^ t • z ∈ R'}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s + t, ?_⟩
    rw [smul_add, pow_add]
    refine R'.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact R'.smul_mem _ hs
    · rw [mul_smul]; exact R'.smul_mem _ ht
  smul_mem' := by
    rintro c z ⟨t, ht⟩
    exact ⟨t, by rw [smul_comm]; exact R'.smul_mem c ht⟩

theorem dvd_pow_of_ne_zero (l : O) (hl : l ∈ IsLocalRing.maximalIdeal O) {r : O} (hr : r ≠ 0) :
    ∃ n : ℕ, r ∣ l ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  have hd : ϖ ∣ l := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hϖ
    rw [hϖ, Ideal.mem_span_singleton] at hl
    exact hl
  exact ⟨n, Units.mul_left_dvd.mpr (pow_dvd_pow_of_dvd hd n)⟩


variable {R : Type} [AddCommGroup R] [Module O R]

abbrev Aq (O : Type) [CommRing O] (k : ℕ) := PowerSeries O ⧸ Ideal.span {(X : PowerSeries O) ^ k}

abbrev Aql (O : Type) [CommRing O] (k c : ℕ) (l : O) :=
  PowerSeries O ⧸ Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)}

theorem spanX_le (k c : ℕ) (l : O) :
    Ideal.span {(X : PowerSeries O) ^ k} ≤ Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)} :=
  Ideal.span_mono (by simp)

def red (k c : ℕ) (l : O) : Aq O k →ₐ[O] Aql O k c l := Ideal.Quotient.factorₐ O (spanX_le k c l)

theorem red_mk (k c : ℕ) (l : O) (a : PowerSeries O) :
    red k c l (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl


theorem smul_Aq (k : ℕ) (a : O) (y : Aq O k) :
    a • y = Ideal.Quotient.mk _ (C a) * y := by
  rw [Algebra.smul_def]; rfl


theorem red_eq_zero (k c : ℕ) (l : O) (y : Aq O k) (h : red k c l y = 0) :
    ∃ z : Aq O k, y = (l ^ c) • z := by
  induction y using Quotient.inductionOn' with | h a => ?_
  have h' : (Ideal.Quotient.mk (Ideal.span {(X : PowerSeries O) ^ k, C (l ^ c)})) a = 0 := h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_pair] at h'
  obtain ⟨u, w, huw⟩ := h'
  refine ⟨Ideal.Quotient.mk _ w, ?_⟩
  rw [smul_Aq]
  change Ideal.Quotient.mk _ a = _
  rw [← huw, ← map_mul, mul_comm (C (l ^ c)) w, Ideal.Quotient.eq, add_sub_cancel_right]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

section Main

variable [Module.Free O R] [Module.Finite O R]


end Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount
end
end

section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LD

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.DCount

section Setup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem ndl_smul (i : ZMod n) {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T} (hx : x ∈ NDl W T i) :
    a • x ∈ NDl W T i := by
  have hx' : x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := hx
  have hD : (letE i : LetA O n) • x = x ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x := hx'.2
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  show a • x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i (a • x)
  refine ⟨(W.N T).smul_mem a hx'.1, ?_, ?_⟩
  · rw [smul_smul, mul_comm, ← smul_smul, hD.1]
  · intro δ hδ
    have hγ : letγ (W.γ₀ δ) a = a := ha' δ hδ
    rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, hD.2 δ hδ, hγ]

theorem phiPull_smul (i : ZMod n) {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T}
    (hx : x ∈ PhiPullΔ W T i) : a • x ∈ PhiPullΔ W T i := by
  have hle : PhiPullΔ W T i ≤
      (PhiPullΔ W T i).comap (a • (LinearMap.id : W.DD T →ₗ[O] W.DD T)) := by
    unfold PhiPullΔ
    rw [Submodule.span_le]
    rintro y ⟨c, hc, z, hz, rfl⟩
    refine Submodule.mem_comap.mpr ?_
    rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    exact Submodule.subset_span ⟨a * c, mul_mem ha hc, z, hz, rfl⟩
  exact hle hx

theorem qp_mem (hπ : W.π₀ ∈ W.AΔ) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := by
  show W.π₀ + ((PD.p : ℕ) : LetA O n) ∈ W.AΔ
  exact add_mem hπ (Subalgebra.natCast_mem _ _)

def QhP (i : ZMod n) (h : ℕ) : Submodule O (W.DD T) :=
  (PhiPullΔ W T i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ h) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))

def Zh (i : ZMod n) (h : ℕ) : Submodule O ↥(NDl W T i) := (QhP W T i h).comap (NDl W T i).subtype

def qN (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) : ↥(NDl W T i) →ₗ[O] ↥(NDl W T i) :=
  (Formalism.MainNotions.LiftingTheory.qp W • (NDl W T i).subtype).codRestrict (NDl W T i)
    (fun x => ndl_smul W T i (qp_mem W hπ) x.2)

theorem qN_apply (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (x : ↥(NDl W T i)) :
    ((qN W T hπ i x : ↥(NDl W T i)) : W.DD T) = Formalism.MainNotions.LiftingTheory.qp W • (x : W.DD T) := rfl

theorem zh_stable (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (h : ℕ) :
    Zh W T i h ≤ (Zh W T i h).comap (qN W T hπ i) := by
  intro x hx
  have hx' : (x : W.DD T) ∈ (PhiPullΔ W T i).map
      ((Formalism.MainNotions.LiftingTheory.qp W ^ h) • (LinearMap.id : W.DD T →ₗ[O] W.DD T)) := hx
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx'
  show ((qN W T hπ i x : ↥(NDl W T i)) : W.DD T) ∈ (PhiPullΔ W T i).map
      ((Formalism.MainNotions.LiftingTheory.qp W ^ h) • (LinearMap.id : W.DD T →ₗ[O] W.DD T))
  rw [qN_apply]
  refine Submodule.mem_map.mpr ⟨Formalism.MainNotions.LiftingTheory.qp W • y, phiPull_smul W T i (qp_mem W hπ) hy, ?_⟩
  rw [← hyx]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [smul_smul, smul_smul, mul_comm]

abbrev RR (i : ZMod n) (h : ℕ) := ↥(NDl W T i) ⧸ Zh W T i h

def qR (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (h : ℕ) : Module.End O (RR W T i h) :=
  (Zh W T i h).mapQ (Zh W T i h) (qN W T hπ i) (zh_stable W T hπ i h)



def RRp (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (h : ℕ) {m' : ℕ} (g : Fin m' → ↥(NDl W T i)) :
    Submodule O (RR W T i h) :=
  Submodule.span O {y | ∃ (a : ℕ) (j : Fin m'), y = (qR W T hπ i h ^ a) (Submodule.Quotient.mk (g j))}

theorem RRp_stable (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (h : ℕ) {m' : ℕ} (g : Fin m' → ↥(NDl W T i)) :
    ∀ x ∈ RRp W T hπ i h g, qR W T hπ i h x ∈ RRp W T hπ i h g := by
  intro x hx
  have hle : RRp W T hπ i h g ≤ (RRp W T hπ i h g).comap (qR W T hπ i h) := by
    unfold RRp
    rw [Submodule.span_le]
    rintro y ⟨a, j, rfl⟩
    refine Submodule.mem_comap.mpr (Submodule.subset_span ⟨a + 1, j, ?_⟩)
    rw [pow_succ']
    rfl
  exact hle hx

private lemma exists_pow_eq_one_mul {Γ : Type} [CommGroup Γ] {a b : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1)
    (hb : ∃ k : ℕ, 0 < k ∧ b ^ k = 1) : ∃ k : ℕ, 0 < k ∧ (a * b) ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  obtain ⟨m, hm, hbm⟩ := hb
  refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hak, one_pow, one_mul, mul_comm, pow_mul, hbm, one_pow]

private lemma exists_pow_eq_one_inv {Γ : Type} [CommGroup Γ] {a : Γ} (ha : ∃ k : ℕ, 0 < k ∧ a ^ k = 1) :
    ∃ k : ℕ, 0 < k ∧ a⁻¹ ^ k = 1 := by
  obtain ⟨k, hk, hak⟩ := ha
  exact ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩

theorem uniformizer_mem_delta_invariants : W.π₀ ∈ W.AΔ := by
  show ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀
  intro δ hδ
  have hδt := (W.DelF_def δ).1 hδ
  funext i
  show W.γ₀ δ W.π₀₁ = W.π₀₁
  simp only [Formalism.BasicNotions.LocWach.π₀₁, map_add, map_sub, map_one, map_natCast, map_sum]
  congr 1
  refine Finset.sum_equiv (Equiv.mulLeft δ) ?_ ?_
  · intro g
    simp only [Equiv.coe_mulLeft]
    rw [W.DelF_def g, W.DelF_def (δ * g)]
    constructor
    · exact fun hg => exists_pow_eq_one_mul hδt hg
    · intro hg
      have h2 := exists_pow_eq_one_mul (exists_pow_eq_one_inv hδt) hg
      rwa [inv_mul_cancel_left] at h2
  · intro g _
    simp only [Equiv.coe_mulLeft, map_mul, AlgHom.mul_apply]

end Setup

section Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def DRData (T : LocLat G Qp LL O) (hπ : W.π₀ ∈ W.AΔ) (i : ZMod n) (h m c ρ : ℕ) : Prop :=
  ∃ (m' : ℕ) (_ : m' ≤ m) (g : Fin m' → ↥(NDl W T i)) (k : Fin m' → ℕ),
    Module.Free O (RR W T i h) ∧ Module.Finite O (RR W T i h) ∧ IsNilpotent (qR W T hπ i h) ∧
    (∃ e : ↥(RRp W T hπ i h g) ≃ₗ[O] ((j : Fin m') → Aq O (k j)),
      ∀ (x : ↥(RRp W T hπ i h g)) (j : Fin m'),
        e ⟨qR W T hπ i h x, RRp_stable W T hπ i h g x x.2⟩ j =
          Ideal.Quotient.mk _ PowerSeries.X * e x j) ∧
    (∀ (z : RR W T i h) (t : ℕ), ((PD.p : ℕ) : O) ^ t • z ∈ RRp W T hπ i h g →
      ((PD.p : ℕ) : O) ^ c • z ∈ RRp W T hπ i h g) ∧
    finrank O (RR W T i h ⧸ satL ((PD.p : ℕ) : O) (RRp W T hπ i h g)) ≤ ρ


theorem geom_mem (hπ : W.π₀ ∈ W.AΔ) (a : ℕ) :
    (∑ s ∈ Finset.range a, Formalism.MainNotions.LiftingTheory.qp W ^ s * ((PD.p : ℕ) : LetA O n) ^ (a - 1 - s)) ∈ W.AΔ :=
  sum_mem fun s _ => mul_mem (pow_mem (qp_mem W hπ) _) (pow_mem (Subalgebra.natCast_mem _ _) _)


def NinQbP [NeZero n] : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → m = 0 → ∀ i ∈ evens n d, ∀ x ∈ NDl W T₂ i,
      x ∈ (PhiPullΔ W T₂ i).map ((Formalism.MainNotions.LiftingTheory.qp W ^ b i) • (LinearMap.id : W.DD T₂ →ₗ[O] W.DD T₂))

end Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LD
end
end
