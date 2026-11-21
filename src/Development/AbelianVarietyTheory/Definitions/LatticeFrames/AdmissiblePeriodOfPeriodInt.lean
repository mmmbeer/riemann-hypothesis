import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PerIntOnAmb
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowF
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGapNonemptyAndRecordNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisor

noncomputable section

namespace GlobalTheory.Core.Int.Model

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

section General

variable (D : D7) (u : D.what₂.Word)





variable {D}

theorem valGe_emb (w : D.what₂.places.Pl) (y : D.what₂.LL) (s : ℝ) :
    ValGe D w (D.what₂.embLL y) s ↔ (y = 0 ∨ s ≤ (vAdd (D.plEq w) y : ℝ)) :=
  ⟨fun ⟨y', h, hv⟩ => D.what₂.embLL.injective h ▸ hv, fun h => ⟨y, rfl, h⟩⟩



theorem vAdd_inv (w : D.what₂.places.Pl) (y : D.what₂.LL) : vAdd (D.plEq w) y⁻¹ = - vAdd (D.plEq w) y := by
  simp [vAdd]





theorem valGe_mul {w : D.what₂.places.Pl} {z z' : ℂ} {s t : ℝ} (h : ValGe D w z s) (h' : ValGe D w z' t) :
    ValGe D w (z * z') (s + t) := by
  obtain ⟨y, rfl, hv⟩ := h
  obtain ⟨y', rfl, hv'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · simp [h0]
  by_cases h1 : y' = 0
  · simp [h1]
  right
  rw [WeilJacquetShalikaLaw.vAdd_mul' _ h0 h1]
  push_cast
  exact add_le_add (hv.resolve_left h0) (hv'.resolve_left h1)

theorem valGe_add {w : D.what₂.places.Pl} {z z' : ℂ} {s : ℝ} (h : ValGe D w z s) (h' : ValGe D w z' s) :
    ValGe D w (z + z') s := by
  obtain ⟨y, rfl, hv⟩ := h
  obtain ⟨y', rfl, hv'⟩ := h'
  exact ⟨y + y', map_add _ _ _, WeightDegreeSizes.pair_add_ge D w hv hv'⟩




theorem per_smul (a : D.what₂.LL) (φ : (D.div.Nu u).V) (F : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 (D.jN u (a • φ)) F = D.what₂.embLL a * D.what₂.perCol u D.what₂.mu0 (D.jN u φ) F := by
  rw [LinearMap.map_smulₛₗ]
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, Examples₂.NZ.col_smul]
  simp

theorem per_add (φ ψ : (D.div.Nu u).V) (F : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 (D.jN u (φ + ψ)) F =
      D.what₂.perCol u D.what₂.mu0 (D.jN u φ) F + D.what₂.perCol u D.what₂.mu0 (D.jN u ψ) F := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_add, Submodule.coe_add, Examples₂.NZ.col_add]
  simp

theorem int_of_valGe {z : ℂ} (h : ∀ w, ValGe D w z 0) (w0 : D.what₂.places.Pl) :
    ∃ y : 𝓞 D.what₂.LL, D.what₂.embLL (y : D.what₂.LL) = z := by
  obtain ⟨y, rfl, -⟩ := h w0
  have : ∀ v : HeightOneSpectrum (𝓞 D.what₂.LL), v.valuation D.what₂.LL y ≤ 1 := by
    intro v
    obtain ⟨w, rfl⟩ := D.plEq.surjective v
    by_cases h0 : y = 0
    · simp [h0]
    have h1 := ((valGe_emb w y 0).1 (h w)).resolve_left h0
    have h2 : (0 : ℤ) ≤ vAdd (D.plEq w) y := by exact_mod_cast h1
    unfold vAdd at h2
    have hne : (D.plEq w).valuation D.what₂.LL y ≠ 0 := by simpa using h0
    rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one D.what₂.LL y this
  exact ⟨c, congrArg _ hc⟩

theorem valGe_of_int (w : D.what₂.places.Pl) (y : 𝓞 D.what₂.LL) : ValGe D w (D.what₂.embLL (y : D.what₂.LL)) 0 := by
  rw [valGe_emb]
  by_cases h0 : (y : D.what₂.LL) = 0
  · exact Or.inl h0
  right
  have h1 : (D.plEq w).valuation D.what₂.LL (y : D.what₂.LL) ≤ 1 := (D.plEq w).valuation_le_one y
  have hne : (D.plEq w).valuation D.what₂.LL (y : D.what₂.LL) ≠ 0 := by simpa using h0
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  have : (0 : ℤ) ≤ vAdd (D.plEq w) (y : D.what₂.LL) := by unfold vAdd; omega
  exact_mod_cast this

theorem nonempty_place : Nonempty D.what₂.places.Pl := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.what₂.LL)
  exact ⟨D.plEq.symm ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩

theorem perIntOn_iff (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : PerIntOn D u N ↔ ∀ w, PerGeOn D u N w 0 := by
  obtain ⟨w0⟩ := nonempty_place (D := D)
  constructor
  · intro h w φ hφ F hF
    obtain ⟨y, hy⟩ := h φ hφ F hF
    exact hy ▸ valGe_of_int w y
  · intro h φ hφ F hF
    exact int_of_valGe (fun w => h w φ hφ F hF) w0

open Classical in
theorem count_shift (S : Finset D.what₂.places.Pl) (n : D.what₂.places.Pl → ℤ) (w : D.what₂.places.Pl) :
    FractionalIdeal.count D.what₂.LL (D.plEq w)
      (∏ w ∈ S, ((D.plEq w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-(n w))) =
      if w ∈ S then - n w else 0 := by
  rw [FractionalIdeal.count_prod _ _ _ _
    (fun b _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq b).ne_bot))]
  have h0 : ∀ b, b ≠ w → FractionalIdeal.count D.what₂.LL (D.plEq w)
      (((D.plEq b).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-(n b))) = 0 := fun b hb => by
    rw [FractionalIdeal.count_zpow, FractionalIdeal.count_maximal_coprime _ _ (fun h => hb (D.plEq.injective h)), mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single w (fun b _ hb => h0 b hb) (fun h' => (h' h).elim), FractionalIdeal.count_zpow_self]
  · exact Finset.sum_eq_zero fun b hb => h0 b (fun e => h (e ▸ hb))

theorem vAdd_eq_count (w : D.what₂.places.Pl) {y : D.what₂.LL} (hy : y ≠ 0) :
    vAdd (D.plEq w) y = FractionalIdeal.count D.what₂.LL (D.plEq w)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) y) := by
  unfold vAdd
  rw [NumeratorIdeal.valuation_eq_count _ _ hy, WithZero.log_exp, neg_neg]

open Classical in

theorem perIntOn_shift_iff (S : Finset D.what₂.places.Pl) (n : D.what₂.places.Pl → ℤ)
    (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) :
    PerIntOn D u (shift D u S n N) ↔ ∀ w, PerGeOn D u N w (((if w ∈ S then n w else 0 : ℤ)) : ℝ) := by
  set I : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL :=
    ∏ w ∈ S, ((D.plEq w).asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-(n w)) with hI
  have hI0 : I ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (D.plEq b).ne_bot)
  have hc : ∀ w, FractionalIdeal.count D.what₂.LL (D.plEq w) I = - (if w ∈ S then n w else 0) := fun w => by
    rw [hI, count_shift]; split_ifs <;> simp
  constructor
  · intro h w φ hφ F hF
    have h1 : ∀ a ∈ I, ∃ y : 𝓞 D.what₂.LL, D.what₂.embLL (y : D.what₂.LL) =
        D.what₂.embLL a * D.what₂.perCol u D.what₂.mu0 (D.jN u φ) F := fun a ha => by
      rw [← per_smul]
      exact h _ (Submodule.subset_span ⟨a, ha, φ, hφ, rfl⟩) F hF
    obtain ⟨a0, ha0, ha0I⟩ : ∃ a : D.what₂.LL, a ≠ 0 ∧ a ∈ I := by
      by_contra hn
      push_neg at hn
      apply hI0
      rw [FractionalIdeal.eq_zero_iff]
      intro x hx
      by_contra hx0
      exact hn x hx0 hx
    obtain ⟨y0, hy0⟩ := h1 a0 ha0I
    have he : D.what₂.embLL a0 ≠ 0 := (map_ne_zero _).2 ha0
    have hy : D.what₂.embLL (y0 / a0) = D.what₂.perCol u D.what₂.mu0 (D.jN u φ) F := by
      rw [map_div₀, hy0]; field_simp
    generalize (y0 : D.what₂.LL) / a0 = y at hy
    refine ⟨y, hy, ?_⟩
    by_cases hy0 : y = 0
    · exact Or.inl hy0
    right
    have hs : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) y ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.2 hy0
    have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) y * I ≤ 1 := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hx
      obtain ⟨c, hc⟩ := h1 a ha
      rw [← hy, ← map_mul] at hc
      exact (FractionalIdeal.mem_one_iff _).2 ⟨c, by rw [mul_comm]; exact D.what₂.embLL.injective hc⟩
    have h2 := FractionalIdeal.count_mono D.what₂.LL (D.plEq w) (mul_ne_zero hs hI0) hle
    rw [FractionalIdeal.count_one, FractionalIdeal.count_mul _ _ hs hI0, hc, ← vAdd_eq_count w hy0] at h2
    have h3 : (if w ∈ S then n w else 0) ≤ vAdd (D.plEq w) y := by omega
    exact_mod_cast h3
  · intro h
    rw [perIntOn_iff]
    intro w φ hφ F hF
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hx
      rw [per_smul]
      have h1 : ValGe D w (D.what₂.embLL a) (-(((if w ∈ S then n w else 0 : ℤ)) : ℝ)) := by
        rw [valGe_emb]
        by_cases ha0 : a = 0
        · exact Or.inl ha0
        right
        have h2 := FractionalIdeal.count_mono D.what₂.LL (D.plEq w) (FractionalIdeal.spanSingleton_ne_zero_iff.2 ha0)
          (FractionalIdeal.spanSingleton_le_iff_mem.2 ha)
        rw [hc, ← vAdd_eq_count w ha0] at h2
        exact_mod_cast h2
      simpa using valGe_mul h1 (h w y hy F hF)
    | zero =>
      have := per_smul u 0 0 F
      rw [zero_smul, map_zero D.what₂.embLL, zero_mul] at this
      exact ⟨0, by rw [this, map_zero], Or.inl rfl⟩
    | add x y _ _ hx hy => rw [per_add]; exact valGe_add hx hy
    | smul a x _ hx =>
      rw [show a • x = (a : D.what₂.LL) • x from (algebraMap_smul D.what₂.LL a x).symm, per_smul]
      simpa using valGe_mul (valGe_of_int w a) hx

theorem gen_mem (μ : D.what₂.Tup) {v : D.what₂.Amb μ} (hv : v ∈ (D.what₂.Mtilde μ).gen) : v ∈ (D.what₂.Mtilde μ).carrier := by
  classical
  refine ⟨fun x => if x = v then 1 else 0, ?_⟩
  rw [Finset.sum_eq_single v (fun b _ hb => by simp [hb]) (fun h => (h hv).elim)]
  simp



end General

section Family

open Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ

abbrev oneCls (n : ℕ) (hn : 0 < n) : ClsPkg where
  cls := fun _ => Unit
  clsFin := fun _ => inferInstance
  stab := fun _ _ => PUnit
  stabGrp := fun _ _ => inferInstance
  stabFin := fun _ _ => inferInstance
  DGam := n
  DGam_pos := hn
  dvd := fun _ _ => by simp

def linePer (z : ℂ) : FK Unit →ₗ[ℂ] En 1 →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun ψ F => z * ψ () () * F 0) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring)

theorem col_one {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (n : ℕ) (hn : 0 < n) (φ : FK Unit) :
    (chainN hc (oneCls n hn)).col φ = φ := by
  have : ∀ m, Formalism.ThetaLiftIndependence.chainOpM (chainN hc (oneCls n hn)).wt (chainN hc (oneCls n hn)).Kmap m φ = φ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      funext c y
      simp [Formalism.ThetaLiftIndependence.chainOpM, Formalism.ThetaLiftIndependence.kerOpM, ih, ColumnChain.Kmap, ColumnChain.divDe, ColumnChain.sharp, mulFun,
        ColumnChain.wt]
  exact this _

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

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (nG : ℕ) (hnG : 0 < nG)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW (fun _ => oneCls nG hnG) T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW (fun _ => oneCls nG hnG) T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ (_ : W) i, Unit → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (z : ℂ)
  (NuL : ∀ _ : W, Submodule (𝓞 H.E) (Unit → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((oneCls nG hnG).cls 0))

local notation "DR" => (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol (fun _ => oneCls nG hnG) T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw 1 1 1 le_rfl Unit (fun _ => ()) (fun _ => ()) Lb hT2 (fun _ _ => linePer z) NuL gat hgat)



theorem mem_std (K : Type) [Field K] [NumberField K] [StarRing K] (x : Unit → K) :
    x ∈ (stdHLat K Unit).L ↔ ∃ c : 𝓞 K, x () = (c : K) := by
  show x ∈ Submodule.span (𝓞 K) (Set.range (Pi.basisFun K Unit)) ↔ _
  rw [Set.range_unique, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by simp [Algebra.smul_def]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by funext i; cases i; simp [Algebra.smul_def, hc]⟩





end Family

end GlobalTheory.Core.Int.Model
