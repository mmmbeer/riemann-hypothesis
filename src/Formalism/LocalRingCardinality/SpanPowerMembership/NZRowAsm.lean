import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowW
import Formalism.LocalRingCardinality.Lemmas
import Mathlib
import Formalism.LocalRingCardinality.SpanPowerMembership.NStageTrivialCharacterCoeffEq
import Formalism.SharpRestriction.InertJacobiLevels.ExtraTheta
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.InertJacobiLevels.ExtraEnt
import Formalism.SharpRestriction.InertJacobiLevels.GaugeExists

section
namespace Formalism.BasicNotions.Examples₂.NZ

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {V : Type*} [AddCommGroup V] [Module R V]

def glue (A : HeightOneSpectrum R → Submodule R V) : Submodule R V := ⨅ w, A w



end Formalism.BasicNotions.Examples₂.NZ
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]

def locS (w : HeightOneSpectrum (𝓞 K)) (B : Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {x | InLoc w B x}
  add_mem' := by
    rintro a b ⟨s, hs, h1⟩ ⟨t, ht, h2⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.smul_mem _ h1
    · rw [mul_smul]; exact B.smul_mem _ h2
  zero_mem' := ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  smul_mem' := by
    rintro r a ⟨s, hs, h1⟩
    exact ⟨s, hs, by rw [smul_comm]; exact B.smul_mem r h1⟩



theorem finite_over (t : 𝓞 K) (ht : t ≠ 0) : {v : HeightOneSpectrum (𝓞 K) | t ∈ v.asIdeal}.Finite := by
  have h : Ideal.span {t} ≠ 0 := by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ht
  exact (Ideal.finite_factors h).subset fun v hv => Ideal.dvd_span_singleton.mpr hv

variable [Module K V] [IsScalarTower (𝓞 K) K V]


end Gen

variable {D : D7} (c : LatCmp D)

structure NuData (c : LatCmp D) where
  S : ℕ → Prop
  S_fin : {p | S p}.Finite
  NPf : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    Submodule (D.gat u w hg).O (D.gat u w hg).Fn

  exists_residueChar_pow_smul_mem : ∀ u w hg, ∃ N : ℕ, ∀ y ∈ DV.MramL D u,
    ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ N • c.cmpN u w hg y ∈ NPf u w hg

  T_abs : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ x : (D.div.Nu u).V,
    ∃ m : ℕ, ∀ a ∈ (D.plEq w).asIdeal ^ m, D.nuIn u (a • x) ∈ LT.Nlam D u w

variable {c} (N : NuData c)

theorem int_mem_intW (w : D.what₂.places.Pl) (r : 𝓞 D.what₂.LL) : (r : D.what₂.LL) ∈ intW D.what₂.places w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one r)

def atT (u : D.what₂.Word) (w : D.what₂.places.Pl) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V where
  carrier := {x | D.nuIn u x ∈ LT.Nlam D u w}
  add_mem' := by
    intro a b ha hb
    show D.nuIn u (a + b) ∈ LT.Nlam D u w
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    show D.nuIn u 0 ∈ LT.Nlam D u w
    rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' := by
    intro r a ha
    show D.nuIn u (r • a) ∈ LT.Nlam D u w
    rw [← algebraMap_smul D.what₂.LL r a, map_smul]
    exact (LT.Nlam D u w).smul_mem (⟨_, int_mem_intW w r⟩ : intW D.what₂.places w) ha

include N in

def srv (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V where
  carrier := {x | c.cmpN u w hg x ∈ N.NPf u w hg}
  add_mem' := by
    intro a b ha hb
    show c.cmpN u w hg (a + b) ∈ N.NPf u w hg
    rw [map_add]; exact Submodule.add_mem _ ha hb
  zero_mem' := by
    show c.cmpN u w hg 0 ∈ N.NPf u w hg
    rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' := by
    intro r a ha
    show c.cmpN u w hg (r • a) ∈ N.NPf u w hg
    obtain ⟨o, ho⟩ := (c.embW_val u w hg _).1 ((D.plEq w).valuation_le_one r)
    rw [← algebraMap_smul D.what₂.LL r a, c.cmpN_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o ha

def cond (u : D.what₂.Word) (w : D.what₂.places.Pl) : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V :=
  if D.what₂.places.resChar w = (D.mem u).A.T then atT u w
  else if h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) ∧ N.S (D.what₂.places.resChar w) then srv N u w h.1
  else locS (D.plEq w) (DV.MramL D u)

theorem inv_mem_intW (w : D.what₂.places.Pl) (s : 𝓞 D.what₂.LL) (hs : s ∉ (D.plEq w).asIdeal) :
    (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s)⁻¹ ∈ intW D.what₂.places w ∧ algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by
  have hv : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL s) = 1 :=
    ((D.plEq w).valuation_eq_one_iff_notMem).2 hs
  have hs0 : algebraMap (𝓞 D.what₂.LL) D.what₂.LL s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  exact ⟨(D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one]), hs0⟩


theorem resChar_mem (w : D.what₂.places.Pl) : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL), D.val_resChar' w, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  have := D.what₂.places.ramIdx_pos w
  omega

variable (hspan : ∀ u, Submodule.span D.what₂.LL (DV.MramL D u : Set (D.div.Nu u).V) = ⊤)

theorem inLoc_of_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) V) {x : V} (h : x ∈ A) : InLoc w A x :=
  ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical Module

section Desc

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  (w : HeightOneSpectrum A)
  {O Kf : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [IsFractionRing O Kf]
  (σ : K →+* Kf) (hσ : ∀ x : K, w.valuation K x ≤ 1 ↔ σ x ∈ Set.range (algebraMap O Kf))

include hσ in

theorem desc {V W ι : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W]
    (φ : V →+ W) (hφ : ∀ (a : K) x, φ (a • x) = σ a • φ x) (b : Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) (B : Submodule A V) (x : V)
    (hx : φ x ∈ Submodule.span O (φ '' (B : Set V))) : ∃ s : A, s ∉ w.asIdeal ∧ s • x ∈ B := by
  have h1 : (1 : A) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  by_cases hx0 : x = 0
  · exact ⟨1, h1, by rw [hx0, smul_zero]; exact B.zero_mem⟩
  have hφx : φ x ≠ 0 :=
    (FBC.li_of_basis_li σ φ hφ b hb (fun _ : Unit => x) (LinearIndependent.of_subsingleton () hx0)).ne_zero ()
  have h2 := (FBC.flat_ext w σ hσ φ hφ b hb).2 B (Submodule.span K {x})
  have h3 : φ x ∈ Submodule.span O (φ '' ((B ⊓ (Submodule.span K {x}).restrictScalars A : Submodule A V) : Set V)) := by
    rw [← h2]
    exact ⟨hx, Submodule.subset_span ⟨x, Submodule.mem_span_singleton_self x, rfl⟩⟩
  by_contra hno
  have hlt : ∀ k : K, k • x ∈ B → w.valuation K k < 1 := by
    intro k hk
    by_contra hge
    rw [not_lt] at hge
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp at hge
    obtain ⟨n, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer k⁻¹ (by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hge)
    refine hno ⟨d, d.2, ?_⟩
    have : (d : A) • x = n • (k • x) := by
      rw [← algebraMap_smul K (d : A), ← algebraMap_smul K n, smul_smul, ← hnd, mul_assoc, mul_comm _ k, ← mul_assoc,
        inv_mul_cancel₀ hk0, one_mul]
    rw [this]
    exact B.smul_mem _ hk
  have h4 : Submodule.span O (φ '' ((B ⊓ (Submodule.span K {x}).restrictScalars A : Submodule A V) : Set V)) ≤
      IsLocalRing.maximalIdeal O • Submodule.span O {φ x} := by
    rw [Submodule.span_le]
    rintro _ ⟨y, ⟨hyB, hyU⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hyU
    have hk := hlt k hyB
    obtain ⟨o, ho⟩ := (hσ k).1 hk.le
    refine Submodule.mem_smul_span_singleton.mpr ⟨o, ?_, ?_⟩
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨o', ho'⟩ := hu.exists_right_inv
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [map_zero] at ho
        have : o = 0 := IsFractionRing.injective O Kf (by rw [ho, map_zero])
        rw [this, zero_mul] at ho'
        exact zero_ne_one ho'
      have h5 : σ k⁻¹ = algebraMap O Kf o' := by
        have := congrArg (algebraMap O Kf) ho'
        rw [map_mul, map_one, ho] at this
        rw [map_inv₀]
        exact inv_eq_of_mul_eq_one_right this
      have h6 := (hσ k⁻¹).2 ⟨o', h5.symm⟩
      rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff (w.valuation K)).mpr hk0)] at h6
      exact absurd hk (not_lt.mpr h6)
    · rw [hφ, ← ho, algebraMap_smul]
  obtain ⟨m, hm, hmx⟩ := Submodule.mem_smul_span_singleton.mp (h4 h3)
  have hu : IsUnit (1 - m) := by
    by_contra hnu
    have : (1 - m) + m ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.maximalIdeal O).add_mem ((IsLocalRing.mem_maximalIdeal _).mpr hnu) hm
    rw [sub_add_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  have h7 : (1 - m) • φ x = 0 := by rw [sub_smul, one_smul, hmx, sub_self]
  exact hφx ((hu.smul_eq_zero).mp h7)

end Desc

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical Module

variable {D : D7} (c : LatCmp D) {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts)

def TAbs (D : D7) : Prop :=
  ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ x : (D.div.Nu u).V,
    ∃ m : ℕ, ∀ a ∈ (D.plEq w).asIdeal ^ m, D.nuIn u (a • x) ∈ LT.Nlam D u w

theorem cand_of_VV {p : ℕ} (h : VV X K (aL L) (bL L) p ≠ ∅) : Cand D L K p := by
  unfold VV at h
  by_contra hc
  rw [if_neg fun h' => hc h'.1] at h
  exact h rfl

theorem VV_fin : {p | VV X K (aL L) (bL L) p ≠ ∅}.Finite := by
  refine (Set.finite_lt_nat ⌈L.sc.X'⌉₊).subset fun p hp => ?_
  have h1 := (cand_of_VV X K hp).2.1
  exact Nat.lt_ceil.mpr h1

theorem cmpN_mem_M (u w hg) (y : (D.div.Nu u).V) (hy : y ∈ DV.MramL D u) : c.cmpN u w hg y ∈ (D.gat u w hg).M := by
  rw [← c.cmp_M u w hg]
  exact Submodule.subset_span ⟨D.nuIn u y, hy, rfl⟩

theorem cmpN_mem_Vram (hv : c.VramDef Y) (u w hg) (y : (D.div.Nu u).V) : c.cmpN u w hg y ∈ Y.Vram u w hg := by
  have h1 : D.nuIn u y ∈ (D.fm u).ramSub := by rw [← D.nuIn_range u]; exact ⟨y, rfl⟩
  have h2 : c.cmpN u w hg y ∈ (Y.Vram u w hg : Set (D.gat u w hg).Fn) := by
    rw [hv u w hg]
    exact Submodule.subset_span ⟨D.nuIn u y, h1, rfl⟩
  exact h2

theorem exists_residueChar_pow_smul_mem (hv : c.VramDef Y) (u w hg) : ∃ N : ℕ, ∀ y ∈ DV.MramL D u,
    ((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ N • c.cmpN u w hg y ∈ NP X Y K u w hg := by
  refine ⟨⌈tauP X K (aL L) (bL L) (D.what₂.places.resChar w)⌉.toNat +
    ∑ t0 ∈ VV X K (aL L) (bL L) (D.what₂.places.resChar w),
      ⌈Sv X K (aL L) (bL L) (D.what₂.places.resChar w) t0⌉.toNat, fun y hy => ?_⟩
  have hM := cmpN_mem_M c u w hg y hy
  have hV := cmpN_mem_Vram c Y hv u w hg y
  rw [pow_add, mul_smul]
  unfold NP
  refine ⟨⟨Submodule.smul_mem _ _ (Submodule.subset_span ⟨∅, Finset.empty_subset _, _, hM, ?_⟩), ?_⟩,
    Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hV)⟩
  · simp [yProd]
  · exact ⟨_, Submodule.smul_mem _ _ hM, rfl⟩

def nuDataOf (hv : c.VramDef Y) (hT : TAbs D) : NuData c where
  S p := VV X K (aL L) (bL L) p ≠ ∅
  S_fin := VV_fin X K
  NPf := NP X Y K
  exists_residueChar_pow_smul_mem := exists_residueChar_pow_smul_mem c X Y K hv
  T_abs := hT

variable (hv : c.VramDef Y) (hT : TAbs D)

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.MainNotions.G Classical Module

variable {D : D7}

def withNu (L : SizeData₂ D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (len : D.what₂.Word → D.what₂.places.Pl → ℚ) : SizeData₂ D :=
  { L with NuLat := N, lenMN := len }

variable (c : LatCmp D) {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts)
  (hv : c.VramDef Y) (hT : TAbs D)

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Gen

variable (D : D7)





end Gen

section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

local notation "DR" => (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)


def levelRecordParameters (L : SizeData₂ DR) : SizeData₂ DR := withNu L (fun u => ((DR).div.Nu u).L) (fun _ _ => 0)



end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂


section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

local notation "DR" => (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)


end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

variable (Wg : TwGap (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat))

local notation "DR" => (withTw (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) Wg)

def fin_X : DivX DR := divXStd DR (fun _ => d0) (fun _ => eb d0) (fun _ => rfl) 1 one_pos

def fin_tw : TwForms DR where
  A := fun u _ => haveI := hT u; atTN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG
  A_T := fun _ _ => rfl
  fm := fun u μ => haveI := hT u; formsN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (En d) (per u μ) H.φ₀ (placesOf H.E)
    (card_realPlaces_eq_degree R)
  e0 := fun _ _ => LinearEquiv.refl _ _
  twist_preserves_base_lattice := fun _ _ _ => Iff.rfl
  embed_mul_block_embedding := fun _ _ _ => rfl
  eMu0 := fun _ _ _ => LinearEquiv.refl _ _
  eMu0_lat := fun _ _ _ _ => Iff.rfl
  eMu0_emb := fun _ _ _ _ => HEq.rfl

theorem fin_nu_le (u : W) (i : ℕ) (j : ℕ) (hj : i ≤ j) :
    ∀ s c, (nuD DR u i s).colLen c ≤ R.N j := fun s c =>
  ((nuD DR u i s).colLen_anti 0 c (Nat.zero_le _)).trans ((nuD_rows DR u i s).trans
    (by show R.k + i * (R.t + 1) ≤ R.k + j * (R.t + 1); have := Nat.mul_le_mul_right (R.t + 1) hj; omega))

def fin_ent (P : EntPl DR) : KerEnt DR (fin_X H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) (fin_tw H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) where
  lam := P.lam
  iL := P.iL
  iL_lam := P.iL_lam
  iL_int := P.iL_int
  Th := fun _ _ w i _ _ => ThE (R.N i) (R.N (i + 1)) ((DR).what₂.places.resChar w)
  VQ := fun _ _ _ _ => (DR).what₂.LL
  ev := fun _ _ _ _ =>
    { toFun := fun v _ => (DR).what₂.embLL v
      map_add' := fun a b => by funext _; simp
      map_smul' := fun a b => by funext _; simp }
  ev_inj := fun _ _ _ _ a b h => (DR).what₂.embLL.injective (congrFun h ())
  prS := fun _ _ w i _ =>
    { toFun := fun v => P.iL w v • (MvPolynomial.aeval (xS (R.N i) ((DR).what₂.places.resChar w))).toLinearMap
      map_add' := fun a b => by rw [map_add, add_smul]; rfl
      map_smul' := fun a b => by rw [smul_eq_mul, map_mul, mul_smul]; rfl }
  prT := fun u _ w i _ =>
    { toFun := fun v I => P.iL w v * indC (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w]
      map_add' := fun a b => by funext I; simp [add_mul]
      map_smul' := fun a b => by
        funext I
        show P.iL w (a * b) * _ = P.iL w a * (P.iL w b * _)
        rw [map_mul, mul_assoc] }
  prT_val := fun u _ w _ i _ _ v' I => by
    rcases indC_01 (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w] with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨v', by simp [h]⟩
  lat_S := by
    intro u μ w _ i _ φ
    have key : ∀ v : (DR).what₂.LL, (∀ J : KM.ColChoice (R.N i) (nuD DR u i),
        ‖P.iL w v * MvPolynomial.eval (xS (R.N i) ((DR).what₂.places.resChar w))
          (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (R.N i) (nuD DR u i) J))‖ ≤ 1) ↔
        v ∈ intW (DR).what₂.places w := fun v => by
      rw [P.iL_int]
      simp only [eval_nablaX]
      constructor
      · intro h
        have := h (initC (nuD DR u i) (fin_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg u i i le_rfl))
        rwa [show (∏ s, ∏ c : Fin ((nuD DR u i s).rowLen 0), if ∀ k,
            ((initC (nuD DR u i) (fin_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg u i i le_rfl)) s c k : ℕ) = k then (1 : ℂ_[(DR).what₂.places.resChar w])
            else 0) = 1 from indC_init (nuD DR u i) _ _, mul_one] at this
      · intro h J
        rcases indC_01 (nuD DR u i) J ℂ_[(DR).what₂.places.resChar w] with h0 | h0 <;>
          · unfold indC at h0
            rw [h0]
            simpa using h
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' := (mem_locW_std DR w (ι := (K u).cls i) x).mp hx
      refine ⟨trivial, fun c => ⟨x c, rfl, fun J => ?_⟩⟩
      have := (key (x c)).mpr (hx' c) J
      rwa [← MvPolynomial.coe_aeval_eq_eval] at this
    · rintro ⟨-, h⟩
      choose v hv1 hv2 using h
      refine ⟨v, (mem_locW_std DR w (ι := (K u).cls i) v).mpr fun c => (key (v c)).mp fun J => ?_, ?_⟩
      · have := hv2 c J
        rwa [← MvPolynomial.coe_aeval_eq_eval]
      · funext c y
        exact congrFun (hv1 c) y
  levelFree_lattice_condition := by
    intro u μ w _ i _ φ
    have key : ∀ v : (DR).what₂.LL, (∀ I : KM.ColChoice (R.N (i + 1)) (nuD DR u i),
        ‖P.iL w v * indC (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w]‖ ≤ 1) ↔
        v ∈ intW (DR).what₂.places w := fun v => by
      rw [P.iL_int]
      constructor
      · intro h
        have := h (initC (nuD DR u i) (fin_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg u i (i + 1) (Nat.le_succ i)))
        rwa [indC_init, mul_one] at this
      · intro h I
        rcases indC_01 (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w] with h0 | h0 <;>
          · rw [h0]
            simpa using h
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' := (mem_locW_std DR w (ι := (K u).cls (i + 1)) x).mp hx
      exact ⟨trivial, fun c => ⟨x c, rfl, (key (x c)).mpr (hx' c)⟩⟩
    · rintro ⟨-, h⟩
      choose v hv1 hv2 using h
      refine ⟨v, (mem_locW_std DR w (ι := (K u).cls (i + 1)) v).mpr fun c => (key (v c)).mp (hv2 c), ?_⟩
      funext c y
      exact congrFun (hv1 c) y
  un := fun _ _ _ _ _ _ => 1
  un_ne := fun _ _ _ _ _ _ => one_ne_zero
  kform := by
    intro u μ w _ i _ c c' v v' hvv I
    have h3 : ((DR).chTw u μ).Kmap i c c' (fun _ => (DR).what₂.embLL v) = fun _ => (DR).what₂.embLL v :=
      chainN_Kmap (hcW u) (K u) i c c' _
    have h4 : (DR).what₂.embLL v' = ((DR).chTw u μ).Kmap i c c' (fun _ => (DR).what₂.embLL v) () := congrFun hvv ()
    have h2 : (DR).what₂.embLL v' = (DR).what₂.embLL v := by rw [h4, h3]
    have hv' : v' = v := (DR).what₂.embLL.injective h2
    subst hv'
    have e1 : MvPolynomial.aeval (xS (R.N i) ((DR).what₂.places.resChar w))
        (KM.applyAt0 (R.N i) (R.N (i + 1)) ((DR).what₂.places.resChar w) (ThE (R.N i) (R.N (i + 1)) _)
          (KM.Gxz (R.N i) (R.N (i + 1)) (nuD DR u i) I)) = indC (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w] := by
      change MvPolynomial.eval (xS (R.N i) ((DR).what₂.places.resChar w)) _ = _
      rw [eval_applyAt0]
      erw [eval_Gxz _ _ _ _ (fin_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg u i i le_rfl)]
      rfl
    show P.iL w v' * indC (nuD DR u i) I _ = 1 * (P.iL w v' * MvPolynomial.aeval (xS (R.N i)
      ((DR).what₂.places.resChar w)) (KM.applyAt0 (R.N i) (R.N (i + 1)) ((DR).what₂.places.resChar w)
        (ThE (R.N i) (R.N (i + 1)) _) (KM.Gxz (R.N i) (R.N (i + 1)) (nuD DR u i) I)))
    rw [e1, one_mul]


theorem fin_lamDef : DV.LamDef DR := row_lamDef H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat
theorem fin_kapR : DV.KapRBase (fin_X H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) := by
  have hi : (RowSide.sharp DR).iota (DR).what₂.mu0 = (LinearMap.id : En d →ₗ[ℂ] En d) :=
    (sharp_iota DR _).trans (rowsN_iota (hd := hd) _)
  exact (kapOf_one (RowSide.sharp DR) _ (iiStar_id _ rfl (fun x y => by rw [hi]; rfl)
    (by rw [hi]; exact Function.surjective_id)) (fun _ _ => rfl)).symm

theorem fin_memTjL (μ j) (x : Fin d0 → H.E) :
    x ∈ Idx.TjL DR μ j ↔ x ∈ (@stdH H.E _ _ H.cmStar d0).L := by
  letI : StarRing H.E := H.cmStar
  have hset : ∀ y : Fin d0 → H.E, (DR).what₂.jMt μ j y ∈ (DR).what₂.TjSet μ j ↔ y ∈ (stdH H.E d0).L := fun y => by
    have e : (DR).what₂.TjSet μ j = (oB (eb d0) (H.φ₀.comp (algebraMap (𝓞 H.E) H.E))).carrier := rowsN_TjSet (hd := hd) μ j
    rw [e]
    exact jB_mem_oB H.φ₀ (eb d0) (algebraMap (𝓞 H.E) H.E) (row_OFull H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) y
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact (hset y).mp hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      exact (stdH H.E d0).L.smul_mem a hy
  · intro hx
    exact Submodule.subset_span ((hset x).mpr hx)

theorem fin_idx : IdxDefs DR (fin_X H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) := by
  letI : StarRing H.E := H.cmStar
  refine ⟨fun μ j w _ _ => (ijIdx_zero _ μ j w ?_).symm, fun μ j w _ _ => (jwIdx_zero DR μ j w ?_).symm⟩
  · ext y
    constructor
    · intro hy
      exact ⟨y, (fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j y).mpr hy, rfl⟩
    · rintro ⟨x, hx, e⟩
      have : y = x := jB_inj H.φ₀ (eb d0) e
      rw [this]
      exact (fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j x).mp hx
  · ext x
    refine (fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j x).trans ?_
    constructor
    · intro hx
      refine ⟨Submodule.subset_span ((fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j x).mpr hx), fun a ha => ?_⟩
      exact (dual_std H.φ₀ (fun z => emb_star H H.φ₀ z) (eb d0) x).mpr hx a
        ((fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j a).mp ha)
    · rintro ⟨-, h⟩
      exact (dual_std H.φ₀ (fun z => emb_star H H.φ₀ z) (eb d0) x).mp fun a ha =>
        h a ((fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j a).mpr ha)

def fin_amb : AmbForm DR (RowSide.sharp DR) := ambOf DR _ (fun _ => d) (fun _ => eb d) (fun _ => rfl)

def fin_char : CentralCharacterOne DR := ⟨(levelRecordCentralCharacterOne H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat).χ, (levelRecordCentralCharacterOne H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat).cen, (levelRecordCentralCharacterOne H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat).one⟩

def finiteBaseSide : BaseLevelRowSide DR := standardBaseSide DR (fin_char H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg)
theorem fin_rr0Def : (finiteBaseSide H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg).s.RRDef := standardBaseSide_latticeDefined DR _ (row_OFull H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)
def finiteAmbientForm : AmbForm DR (finiteBaseSide H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg).s := standardAmbientForm DR _

end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.Inhab NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Classical.propDecidable

section Conj

variable (V : Type) [AddCommGroup V] [Module ℂ V]

def cj (v : V) : V :=
  (Module.Basis.ofVectorSpace ℂ V).repr.symm
    (((Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _))

theorem cj_add (v w : V) : cj V (v + w) = cj V v + cj V w := by
  unfold cj
  rw [map_add, Finsupp.mapRange_add (fun a b => map_add (starRingEnd ℂ) a b), map_add]

theorem cj_smul (c : ℂ) (v : V) : cj V (c • v) = star c • cj V v := by
  unfold cj
  have : (c • (Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _) =
      star c • ((Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _) := by
    ext i
    simp
  rw [LinearEquiv.map_smul (Module.Basis.ofVectorSpace ℂ V).repr c v, this, LinearEquiv.map_smul]

theorem cj_cj (v : V) : cj V (cj V v) = v := by
  unfold cj
  rw [LinearEquiv.apply_symm_apply]
  have : (((Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _)).mapRange
      (starRingEnd ℂ) (map_zero _) = (Module.Basis.ofVectorSpace ℂ V).repr v := by
    ext i
    simp
  rw [this, LinearEquiv.symm_apply_apply]

end Conj

variable (D : D7)

abbrev HR : Type := lp (fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2

abbrev HC : Type := lp (fun u : D.what₂.Word => D.what₂.Mu u) 2

abbrev HF : Type := HR D × HC D

def petH (a b : HF D) : ℂ := inner ℂ a.1 b.1 + inner ℂ a.2 b.2

def rowI (μ : D.what₂.Tup) (j : ℕ) : D.what₂.Mult μ j →ₗ[ℂ] HF D :=
  (LinearMap.inl ℂ (HR D) (HC D)).comp
    (lp.lsingle (𝕜 := ℂ) (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩)

def rowP (μ : D.what₂.Tup) (j : ℕ) : HF D →ₗ[ℂ] D.what₂.Mult μ j :=
  (lp.evalₗ (𝕜 := ℂ) (fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩).comp
    (LinearMap.fst ℂ (HR D) (HC D))

def colI (u : D.what₂.Word) : D.what₂.Mu u →ₗ[ℂ] HF D :=
  (LinearMap.inr ℂ (HR D) (HC D)).comp
    (lp.lsingle (𝕜 := ℂ) (E := fun u : D.what₂.Word => D.what₂.Mu u) 2 u)

theorem component_inclusion (μ j) (x : D.what₂.Mult μ j) : rowP D μ j (rowI D μ j x) = x :=
  lp.single_apply_self (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩ x

theorem pet_rowI (μ j) (x : D.what₂.Mult μ j) (b : HF D) : petH D (rowI D μ j x) b = inner ℂ x (rowP D μ j b) := by
  show inner ℂ (lp.single (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩ x) b.1 +
    inner ℂ (0 : HC D) b.2 = _
  rw [inner_zero_left, add_zero]
  exact lp.inner_single_left (G := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) ⟨μ, j⟩ x b.1


def toTop {M : Type} [AddCommGroup M] [Module ℂ M] (f : M →ₗ[ℂ] HF D) : M →ₗ[ℂ] (⊤ : Submodule ℂ (HF D)) :=
  f.codRestrict ⊤ fun _ => Submodule.mem_top

def thetaFull : ThetaX D where
  AF := fun _ => HF D
  cusp := fun _ => ⊤
  pet := fun _ F G => petH D F G
  pet_add_left := fun _ F F' G => by
    simp only [petH, Prod.fst_add, Prod.snd_add, inner_add_left]; ring
  pet_smul_left := fun _ c F G => by
    simp only [petH, Prod.smul_fst, Prod.smul_snd, inner_smul_left, mul_add]; rfl
  pet_right := fun _ F => ⟨fun G G' => by
      simp only [petH, Submodule.coe_add, Prod.fst_add, Prod.snd_add, inner_add_right]; ring,
    fun c G => by
      simp only [petH, Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, inner_smul_right, smul_eq_mul, mul_add]⟩
  pet_symm := fun _ F G => by
    simp only [petH, star_add]
    rw [← starRingEnd_apply, ← starRingEnd_apply, inner_conj_symm, inner_conj_symm]
  pet_pos := fun _ F hF => by
    have h1 : (F : HF D) ≠ 0 := fun h => hF (Subtype.ext h)
    have e : (petH D (F : HF D) F).re = ‖(F : HF D).1‖ ^ 2 + ‖(F : HF D).2‖ ^ 2 := by
      simp only [petH, Complex.add_re]
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
    show 0 < (petH D (F : HF D) F).re
    rw [e]
    rcases (not_and_or.mp fun h : (F : HF D).1 = 0 ∧ (F : HF D).2 = 0 => h1 (Prod.ext h.1 h.2)) with h | h
    · have := norm_pos_iff.mpr h; positivity
    · have := norm_pos_iff.mpr h; positivity
  actR := fun _ _ _ => 1
  actR_one := fun _ _ => rfl
  actR_mul := fun _ _ _ _ _ _ => (one_mul _).symm
  actR_cusp := fun _ _ _ _ _ _ => Submodule.mem_top
  Gf := fun _ => PUnit
  actF := fun _ => 1
  actF_cusp := fun _ _ _ _ => Submodule.mem_top
  actF_actR := fun _ _ _ _ => rfl
  Ksph := fun _ _ => ⊤
  Ksph_mono := fun _ _ _ _ => le_refl _
  typ := fun _ _ => ⊤
  Chr := Multiplicative (D.what₂.Tau → ℚ)
  infTy := fun χ τ => Multiplicative.toAdd χ τ
  infTy_mul := fun _ _ _ => rfl
  chrOf := fun _ j => Multiplicative.ofAdd (chrExp D j)
  chrOf_inf := fun _ j τ => by
    show chrExp D (j.1 + 1) τ = _
    unfold chrExp
    rw [dif_pos ⟨Nat.le_add_left _ _, j.2⟩]
    rfl
  etaT := Multiplicative.ofAdd fun _ => 1 / 2
  etaT_inf := fun _ => Or.inl rfl
  etaT_pos := fun _ => rfl
  Sch := fun _ _ => HF D →ₗ[ℂ] HF D
  fact := fun _ _ => Set.univ
  kfin := fun _ _ => ⊤
  th := fun _ _ _ _ => LinearMap.lcomp ℂ (HF D) (⊤ : Submodule ℂ (HF D)).subtype
  Xs := fun t => (tow D t).Xs
  Xs_rank := fun t => (tow D t).Xs_rank
  Xs_sig := fun t => (tow D t).Xs_sig
  Ys := fun t => (tow D t).Ys
  Ys_rank := fun t => (tow D t).Ys_rank
  Ys_sig := fun t => (tow D t).Ys_sig
  iXYs := fun t => (tow D t).iXYs
  iXYs_isom := fun t => (tow D t).iXYs_isom
  iYXm := fun t => (tow D t).iYXm
  iYXm_isom := fun t => (tow D t).iYXm_isom
  YsLow := fun t j _ => (tow D t).Ys j
  YsLow_zero := fun _ _ => rfl
  Xs_rec := fun j _ => by rw [tow_rec]; rfl
  Ys_rec := fun j _ => by rw [tow_rec]; rfl
  conjAF := fun _ => cj (HF D)
  conjAF_add := fun _ => cj_add _
  conjAF_smul := fun _ => cj_smul _
  conjAF_conjAF := fun _ => cj_cj _
  conjAF_cusp := fun _ _ _ => Submodule.mem_top
  Pos := fun _ _ _ => PUnit
  FJd := fun _ _ _ => PUnit
  Bper := fun _ _ _ _ _ _ _ => 0
  Bper_right := fun _ _ _ _ _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  Bper_add_left := fun _ _ _ _ _ _ _ _ => by simp
  Bper_smul_left := fun _ _ _ _ _ _ _ _ => by simp
  Bper_odd := fun _ _ _ _ _ _ _ _ _ => rfl
  Btop := fun _ _ _ _ _ => 0
  Btop_right := fun _ _ _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  Btop_add_left := fun _ _ _ _ _ _ => by simp
  Btop_smul_left := fun _ _ _ _ _ _ => by simp
  pos1 := fun _ => PUnit.unit
  posSym := fun _ => PUnit.unit
  colAF := fun u _ _ => toTop D (colI D u)
  rowAF := fun μ j => toTop D (rowI D μ j)
  PhiY := fun μ j => (rowI D μ j).comp ((D.what₂.io μ j).comp (rowP D μ (j + 1)))
  PhiYup := fun _ _ => 0
  mY := fun _ _ => 1
  mY_pos := fun _ _ => one_pos
  adelicDataRowMeasureScale_trivialTuple := fun _ => rfl
  mY_zero := fun _ => rfl

theorem thetaFull_mY (μ : D.what₂.Tup) (j : ℕ) : (((thetaFull D).mY μ j : ℝ) : ℂ) = 1 := Complex.ofReal_one

theorem thetaFull_row : (thetaFull D).TieRowIsom := fun μ j _ x y => by
  unfold ThetaX.petY
  rw [thetaFull_mY, one_mul]
  exact (pet_rowI D μ j x (rowI D μ j y)).trans (by rw [component_inclusion])

theorem thetaFull_io : (thetaFull D).TieIo := fun μ j _ y x => by
  unfold ThetaX.petY ThetaX.dnY
  rw [thetaFull_mY, thetaFull_mY, one_mul, one_smul]
  show petH D (rowI D μ j (D.what₂.io μ j (rowP D μ (j + 1) (rowI D μ (j + 1) y)))) (rowI D μ j x) = _
  rw [component_inclusion, pet_rowI, component_inclusion]


theorem theta_exists : ∃ X : ThetaX D, X.TieRowIsom ∧ X.TieIo :=
  ⟨thetaFull D, thetaFull_row D, thetaFull_io D⟩

end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.Inhab NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Classical.propDecidable

variable (D : D7)

abbrev HG : Type := WithLp 2 (HR D × WithLp 2 (HC D × ℂ))

def rowJ (μ : D.what₂.Tup) (j : ℕ) : D.what₂.Mult μ j →ₗ[ℂ] HG D :=
  (WithLp.linearEquiv 2 ℂ (HR D × WithLp 2 (HC D × ℂ))).symm.toLinearMap.comp
    ((LinearMap.inl ℂ (HR D) (WithLp 2 (HC D × ℂ))).comp
      (lp.lsingle (𝕜 := ℂ) (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩))

def rowQ (μ : D.what₂.Tup) (j : ℕ) : HG D →ₗ[ℂ] D.what₂.Mult μ j :=
  (lp.evalₗ (𝕜 := ℂ) (fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩).comp
    (WithLp.fstₗ 2 ℂ (HR D) (WithLp 2 (HC D × ℂ)))

def colJ (u : D.what₂.Word) : D.what₂.Mu u →ₗ[ℂ] HG D :=
  (WithLp.linearEquiv 2 ℂ (HR D × WithLp 2 (HC D × ℂ))).symm.toLinearMap.comp
    ((LinearMap.inr ℂ (HR D) (WithLp 2 (HC D × ℂ))).comp
      ((WithLp.linearEquiv 2 ℂ (HC D × ℂ)).symm.toLinearMap.comp
        ((LinearMap.inl ℂ (HC D) ℂ).comp (lp.lsingle (𝕜 := ℂ) (E := fun u : D.what₂.Word => D.what₂.Mu u) 2 u))))

def v0 : HG D := WithLp.toLp 2 (0, WithLp.toLp 2 (0, 1))

theorem v0_ne : v0 D ≠ 0 := fun h => by
  have := congrArg (fun x : HG D => x.snd.snd) h
  exact one_ne_zero this

theorem rowQ_rowJ (μ j) (x : D.what₂.Mult μ j) : rowQ D μ j (rowJ D μ j x) = x :=
  lp.single_apply_self (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩ x

theorem inner_rowJ (μ j) (x : D.what₂.Mult μ j) (b : HG D) : inner ℂ (rowJ D μ j x) b = inner ℂ x (rowQ D μ j b) := by
  rw [WithLp.prod_inner_apply]
  show inner ℂ (lp.single (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩ x) b.fst +
    inner ℂ (0 : WithLp 2 (HC D × ℂ)) b.snd = _
  rw [inner_zero_left, add_zero]
  exact lp.inner_single_left (G := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) ⟨μ, j⟩ x b.fst

def toTopG {M : Type} [AddCommGroup M] [Module ℂ M] (f : M →ₗ[ℂ] HG D) : M →ₗ[ℂ] (⊤ : Submodule ℂ (HG D)) :=
  f.codRestrict ⊤ fun _ => Submodule.mem_top

def Zsp : HSp D := posSpace star_isIntegral 0

theorem ne_Zsp {V : HSp D} (h : 0 < V.rank) : V ≠ Zsp D := fun e => by
  rw [e] at h
  exact lt_irrefl 0 h

def thG (W : HSp D) : (HG D →ₗ[ℂ] HG D) →ₗ[ℂ] (⊤ : Submodule ℂ (HG D)) →ₗ[ℂ] HG D :=
  if W = Zsp D then 0 else LinearMap.lcomp ℂ (HG D) (⊤ : Submodule ℂ (HG D)).subtype


theorem thG_pos {W : HSp D} (h : 0 < W.rank) (Φ F) : thG D W Φ F = Φ F := by
  unfold thG; rw [if_neg (ne_Zsp D h)]; rfl

def ysLow (t j : ℕ) : ℕ → HSp D
  | 0 => (tow D t).Ys j
  | _ + 1 => Zsp D

def thetaG : ThetaX D where
  AF := fun _ => HG D
  cusp := fun _ => ⊤
  pet := fun _ F G => inner ℂ F (G : HG D)
  pet_add_left := fun _ F F' G => inner_add_left _ _ _
  pet_smul_left := fun _ c F G => inner_smul_left _ _ _
  pet_right := fun _ F => ⟨fun G G' => inner_add_right _ _ _, fun c G => inner_smul_right _ _ _⟩
  pet_symm := fun _ F G => (inner_conj_symm (𝕜 := ℂ) (F : HG D) (G : HG D)).symm
  pet_pos := fun _ F hF => by
    have h1 : (F : HG D) ≠ 0 := fun h => hF (Subtype.ext h)
    show 0 < (inner ℂ (F : HG D) (F : HG D)).re
    have e := inner_self_eq_norm_sq (𝕜 := ℂ) (F : HG D)
    have e' : (inner ℂ (F : HG D) (F : HG D)).re = ‖(F : HG D)‖ ^ 2 := e
    rw [e']
    have := norm_pos_iff.mpr h1
    positivity
  actR := fun _ _ _ => 1
  actR_one := fun _ _ => rfl
  actR_mul := fun _ _ _ _ _ _ => (one_mul _).symm
  actR_cusp := fun _ _ _ _ _ _ => Submodule.mem_top
  Gf := fun _ => PUnit
  actF := fun _ => 1
  actF_cusp := fun _ _ _ _ => Submodule.mem_top
  actF_actR := fun _ _ _ _ => rfl
  Ksph := fun _ _ => ⊤
  Ksph_mono := fun _ _ _ _ => le_refl _
  typ := fun _ _ => ⊤
  Chr := Multiplicative (D.what₂.Tau → ℚ)
  infTy := fun χ τ => Multiplicative.toAdd χ τ
  infTy_mul := fun _ _ _ => rfl
  chrOf := fun _ j => Multiplicative.ofAdd (chrExp D j)
  chrOf_inf := fun _ j τ => by
    show chrExp D (j.1 + 1) τ = _
    unfold chrExp
    rw [dif_pos ⟨Nat.le_add_left _ _, j.2⟩]
    rfl
  etaT := Multiplicative.ofAdd fun _ => 1 / 2
  etaT_inf := fun _ => Or.inl rfl
  etaT_pos := fun _ => rfl
  Sch := fun _ _ => HG D →ₗ[ℂ] HG D
  fact := fun _ _ => Set.univ
  kfin := fun _ _ => ⊤
  th := fun _ W _ _ => thG D W
  Xs := fun t => (tow D t).Xs
  Xs_rank := fun t => (tow D t).Xs_rank
  Xs_sig := fun t => (tow D t).Xs_sig
  Ys := fun t => (tow D t).Ys
  Ys_rank := fun t => (tow D t).Ys_rank
  Ys_sig := fun t => (tow D t).Ys_sig
  iXYs := fun t => (tow D t).iXYs
  iXYs_isom := fun t => (tow D t).iXYs_isom
  iYXm := fun t => (tow D t).iYXm
  iYXm_isom := fun t => (tow D t).iYXm_isom
  YsLow := ysLow D
  YsLow_zero := fun _ _ => rfl
  Xs_rec := fun j _ => by rw [tow_rec]; rfl
  Ys_rec := fun j _ => by rw [tow_rec]; rfl
  conjAF := fun _ => cj (HG D)
  conjAF_add := fun _ => cj_add _
  conjAF_smul := fun _ => cj_smul _
  conjAF_conjAF := fun _ => cj_cj _
  conjAF_cusp := fun _ _ _ => Submodule.mem_top
  Pos := fun _ _ _ => PUnit
  FJd := fun _ _ _ => PUnit
  Bper := fun _ _ _ _ _ φ F => inner ℂ φ (F : HG D)
  Bper_right := fun _ _ _ _ _ φ => ⟨fun G G' => inner_add_right _ _ _, fun c G => inner_smul_right _ _ _⟩
  Bper_add_left := fun _ _ _ _ _ _ _ _ => inner_add_left _ _ _
  Bper_smul_left := fun _ _ _ _ _ _ _ _ => inner_smul_left _ _ _
  Bper_odd := fun _ _ _ _ _ _ _ _ _ => rfl
  Btop := fun _ _ _ φ F => inner ℂ φ (F : HG D)
  Btop_right := fun _ _ _ φ => ⟨fun G G' => inner_add_right _ _ _, fun c G => inner_smul_right _ _ _⟩
  Btop_add_left := fun _ _ _ _ _ _ => inner_add_left _ _ _
  Btop_smul_left := fun _ _ _ _ _ _ => inner_smul_left _ _ _
  pos1 := fun _ => PUnit.unit
  posSym := fun _ => PUnit.unit
  colAF := fun u _ _ => toTopG D (colJ D u)
  rowAF := fun μ j => toTopG D (rowJ D μ j)
  PhiY := fun μ j => (rowJ D μ j).comp ((D.what₂.io μ j).comp (rowQ D μ (j + 1)))
  PhiYup := fun _ _ => 0
  mY := fun _ _ => 1
  mY_pos := fun _ _ => one_pos
  adelicDataRowMeasureScale_trivialTuple := fun _ => rfl
  mY_zero := fun _ => rfl

theorem thetaG_mY (μ : D.what₂.Tup) (j : ℕ) : (((thetaG D).mY μ j : ℝ) : ℂ) = 1 := Complex.ofReal_one

theorem rankY_pos (t j : ℕ) (hj : j ≤ D.R.m) : 0 < ((tow D t).Ys j).rank := by
  rw [(tow D t).Ys_rank j hj]
  have := D.R.two_le_m
  unfold Ranks.r
  omega

theorem rankX_pos (t j : ℕ) (hj : j ≤ D.R.m) : 0 < ((tow D t).Xs j).rank := by
  rw [(tow D t).Xs_rank j hj]
  have := D.R.m_add_three_le_k
  omega

theorem spY_pos (j : ℕ) (hj : j ≤ D.R.m) : 0 < (D.sp.Y j).rank := by
  have := rankY_pos D D.R.t j hj
  rwa [tow_rec] at this



theorem thetaG_io : (thetaG D).TieIo := fun μ j hj y x => by
  unfold ThetaX.petY ThetaX.dnY
  rw [thetaG_mY, thetaG_mY, one_mul, one_smul]
  show inner ℂ (thG D (D.sp.Y j) ((rowJ D μ j).comp ((D.what₂.io μ j).comp (rowQ D μ (j + 1))))
    (toTopG D (rowJ D μ (j + 1)) y)) (rowJ D μ j x) = _
  rw [thG_pos D (spY_pos D j hj.le)]
  show inner ℂ (rowJ D μ j (D.what₂.io μ j (rowQ D μ (j + 1) (rowJ D μ (j + 1) y)))) (rowJ D μ j x) = _
  rw [rowQ_rowJ, inner_rowJ, rowQ_rowJ]



theorem cj_ne {V : Type} [AddCommGroup V] [Module ℂ V] {v : V} (h : v ≠ 0) : cj V v ≠ 0 := fun e => h (by
  have := congrArg (cj V) e
  rw [cj_cj] at this
  rw [this]
  have h0 := cj_smul V 0 (0 : V)
  simpa using h0)

theorem inner_self_ne {v : HG D} (h : v ≠ 0) : inner ℂ v v ≠ 0 := inner_self_ne_zero.mpr h


def muOf (P : TPar D) (j : ℕ) : Multiplicative (D.what₂.Tau → ℚ) :=
  Multiplicative.ofAdd fun τ => if h : 1 ≤ j ∧ j ≤ D.R.m then -P.e τ ⟨j - 1, by omega⟩ else 0





theorem cj_zero (V : Type) [AddCommGroup V] [Module ℂ V] : cj V 0 = 0 := by
  have h0 := cj_smul V 0 (0 : V)
  simpa using h0

theorem key3 (W W' : HSp D) (hW' : 0 < W'.rank) (Φ' : HG D →ₗ[ℂ] HG D) (φ' F : (⊤ : Submodule ℂ (HG D)))
    (h1 : inner ℂ (cj (HG D) (thG D W Φ' φ')) (F : HG D) ≠ 0) :
    ∃ Φ : HG D →ₗ[ℂ] HG D, inner ℂ (cj (HG D) (φ' : HG D)) (thG D W' Φ F) ≠ 0 := by
  have hF : (F : HG D) ≠ 0 := fun e => h1 (by rw [e, inner_zero_right])
  have hφ : (φ' : HG D) ≠ 0 := fun e => h1 (by
    have e' : φ' = 0 := Subtype.ext e
    rw [e', map_zero, cj_zero, inner_zero_left])
  refine ⟨(innerₛₗ ℂ (F : HG D)).smulRight (cj (HG D) (φ' : HG D)), ?_⟩
  rw [thG_pos D hW']
  show inner ℂ (cj (HG D) (φ' : HG D)) (inner ℂ (F : HG D) (F : HG D) • cj (HG D) (φ' : HG D)) ≠ 0
  rw [inner_smul_right]
  exact mul_ne_zero (inner_self_ne D hF) (inner_self_ne D (cj_ne hφ))







end Formalism.BasicNotions.Examples₂.NZ
end
end

section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

variable (Wg : TwGap (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat))

local notation "DF" => (withTw (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) Wg)

structure ExtraNZIn (L : SizeData₂ DF) (hT : GatTies DF) (Gi : Formalism.MainNotions.G.Inst DF L) (Gl : Formalism.MainNotions.G.LatInst DF) (K0 : Formalism.MainNotions.G.Consts)
    (cX : ExtraC) where
  le : Formalism.MainNotions.Inhab.LevErr DF
  cmp : LatCmp DF
  latD : LatDefs DF L Gi Gl K0 cmp
  ker : ∀ u w (h : GIdx (DF).host ((DF).mem u).A.T ((DF).what₂.places.resChar w)),
    haveI : Fact ((DF).what₂.places.resChar w).Prime := ⟨(DF).what₂.places.resChar_prime w⟩
    LocalToGlobal₂ DF hT cmp (fin_tw H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) u w h (Gl.Ch u w h)
  P : EntPl DF
  ent_lam : ∀ u w (h : GIdx (DF).host ((DF).mem u).A.T ((DF).what₂.places.resChar w)), (ker u w h).lam = P.lam w
  ep_def : Formalism.MainNotions.G.EpDef Gi cX.Ce
  ep_tie : EpTie Gi
  kapI_def : Formalism.MainNotions.G.KapIDef Gi K0
  fills_all : FillsAll hT Gl
  nu_unserved : NuUnserved Gi K0
  kap_def : DV.KapDef DF
  large : cX.err.Large
  edef : L.EDef le.errX K0 cX.err
  dgamK : ∀ u, (K u).DGam = (K u0).DGam
  nch : NChoice DF
  nch_tie : NChTie DF nch
  nmj : NMj DF (fin_X H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) nch
  fdef : L.FDef
  duStar_def : ∀ u, (((DF).mem u).A.duStar : ℝ) = Formalism.MainNotions.StandardLattice.duStarU DF u
  Dstar_def : (DF).what₂.Dstar = Formalism.MainNotions.StandardLattice.DstarD DF
  gauge : Formalism.MainNotions.Inhab.GaugeExists (DF).host (DF).sp

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

def extraNZ {L : SizeData₂ DF} {hT : GatTies DF} {Gi : Formalism.MainNotions.G.Inst DF L} {Gl : Formalism.MainNotions.G.LatInst DF} {K0 : Formalism.MainNotions.G.Consts} {cX : ExtraC}
    (I : ExtraNZIn H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg L hT Gi Gl K0 cX) : Extra DF L hT Gi Gl K0 (fin_X H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) cX where
  lev := I.le.lev
  th := thetaG DF
  th_io := thetaG_io DF
  cmp := I.cmp
  lat := I.latD
  tw := fin_tw H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg
  ker := I.ker
  ep_def := I.ep_def
  ep_tie := I.ep_tie
  kapI_def := I.kapI_def
  fills_all := I.fills_all
  nu_unserved := I.nu_unserved
  idx := fin_idx H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg
  kap_def := I.kap_def
  lam_def := fin_lamDef H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg
  kapR_def := fin_kapR H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg
  errX := I.le.errX
  err := ⟨I.large, I.le.piG_lev, I.le.piT_lev, I.le.seen, I.le.tauOf,
    Formalism.MainNotions.Inhab.dGamDef_of DF fun u _ => I.dgamK u, I.edef⟩
  nch := I.nch
  nch_tie := I.nch_tie
  xd := Formalism.MainNotions.Inhab.thDataZero DF
  p0 := finiteBaseSide H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg
  rationalRoots_def := fin_rr0Def H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg
  amb := fin_amb H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg
  amb0 := finiteAmbientForm H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg
  fdef := I.fdef
  duStar_def := I.duStar_def
  Dstar_def := I.Dstar_def
  gauge := I.gauge.choose
  gauge_def := I.gauge.choose_spec

end Rec

end Formalism.BasicNotions.Examples₂.NZ
end
end
