import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowE

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Pure

variable {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ)
  (hstar : ∀ z, σ (star z) = starRingEnd ℂ (σ z)) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)

theorem inner_jB (a x : Fin n → K) :
    inner ℂ (jB σ b a) (jB σ b x) = ∑ i, starRingEnd ℂ (σ (a i)) * σ (x i) := by
  rw [← b.repr.inner_map_map, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_jB, repr_jB, RCLike.inner_apply, mul_comm]

theorem star_int (c : 𝓞 K) : ∃ c' : 𝓞 K, star (c : K) = (c' : K) :=
  ⟨⟨star (c : K), map_isIntegral_int (starRingEnd K) (RingOfIntegers.isIntegral_coe c)⟩, rfl⟩

include hstar in

theorem dual_std (x : Fin n → K) :
    (∀ a ∈ (stdH K n).L, ∃ c : 𝓞 K, inner ℂ (jB σ b a) (jB σ b x) = σ (c : K)) ↔ x ∈ (stdH K n).L := by
  constructor
  · intro h
    rw [mem_stdL]
    intro i
    obtain ⟨c, hc⟩ := h (Pi.basisFun K (Fin n) i) (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨c, σ.injective ?_⟩
    rw [← hc, inner_jB, Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [Pi.basisFun_apply, Pi.single_eq_of_ne hk, map_zero, map_zero, zero_mul]
    · simp
  · intro hx a ha
    rw [mem_stdL] at hx ha
    choose cx hcx using hx
    choose ca hca using ha
    choose ca' hca' using fun i => star_int (ca i)
    refine ⟨∑ i, ca' i * cx i, ?_⟩
    have hc : ((∑ i, ca' i * cx i : 𝓞 K) : K) = ∑ i, star (a i) * x i := by
      rw [show ((∑ i, ca' i * cx i : 𝓞 K) : K) = algebraMap (𝓞 K) K (∑ i, ca' i * cx i) from rfl, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hca i, hcx i, hca' i]
    rw [inner_jB, hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hstar]

end Pure

section Sharp

variable (D : D7)

theorem sharp_downTo (μ) (j : ℕ) : (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RowSide.sharp D).downTo μ j).comp (D.what₂.io μ j) = (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [ih]; rfl

theorem sharp_iota (μ) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [sharp_downTo]; rfl

theorem sharp_Usp (μ) : (RowSide.sharp D).Usp μ = D.what₂.Usp μ := by
  unfold RowSide.Usp Rows.Data.Usp
  rw [sharp_iota]; rfl

theorem sharp_Qsp (μ) : (RowSide.sharp D).Qsp μ = D.what₂.Qsp μ := by
  unfold RowSide.Qsp Rows.Data.Qsp
  rw [sharp_Usp]; rfl

theorem starProj_congr {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {A B : Submodule ℂ V}
    (h : A = B) (iA : A.HasOrthogonalProjection) (iB : B.HasOrthogonalProjection) (x : V) :
    A.starProjection x = B.starProjection x := by
  subst h; rfl

theorem sharp_LamSet (μ) : (RowSide.sharp D).LamSet μ = D.what₂.LamSet μ := by
  unfold RowSide.LamSet Rows.Data.LamSet
  exact Set.image_congr' fun x => starProj_congr (sharp_Qsp D μ) _ _ x

theorem sharp_RRset (μ) : (RowSide.sharp D).RRset μ = D.what₂.RRset μ := by
  unfold RowSide.RRset Rows.Data.RRset
  rw [sharp_iota, sharp_LamSet]; rfl


end Sharp

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

theorem row_OFull : OFull DR := fun z =>
  ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩




def levelRecordDivisor : DivX DR := divXStd DR (fun _ => d0) (fun _ => eb d0) (fun _ => rfl) 1 one_pos


theorem row_lamDef : DV.LamDef DR := by
  refine lamDef_of DR fun μ j π x _ => ?_
  have h : (DR).what₂.thetaT μ j = (LinearMap.id : En d0 →ₗ[ℂ] En d0) := rowsN_thetaT (hd := hd) μ j
  rw [h]
  show x = ((1 : ℝ) : ℂ) • x
  simp







def levelRecordCentralCharacterOne : CentralCharacterOne DR where
  χ := omL H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg) ht
  cen := idempotent_mem_center _
  one := by
    have key : (⟨(DR).ntypes.e0, idempotent_mem_center _⟩ :
        Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (ndG H Lb (rowsHN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per) (nHypN H hcW K Dst kb ks tw htw d Dall d0 hd FT ft ft0 per hg))))) =
        ⟨_, labelIdempotent_mem_center H Lb _ _⟩ := Subtype.ext (labelNewtypes_idempotent_eq H Lb _ _ ht G.tame)
    exact (congrArg _ key).trans (labelCharacter_idempotent_one H Lb _ _ ht)

def levelRecordBaseSide : BaseLevelRowSide DR := standardBaseSide DR (levelRecordCentralCharacterOne H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)



end Rec

end Formalism.BasicNotions.Examples₂.NZ
