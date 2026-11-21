import Formalism.SizeWindowBrackets.SBrDiv
import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize

open Module NumberField IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LBrDiv

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2












theorem construct_parameter_definitions : MkParDefs := by
  intro H _ _ _ W _ m G cHH D ell N TT T2 a w Fm
  have hL : (mkData G cHH D ell N TT T2 a w Fm).L = G.x ^ G.ε := by
    show Real.log (bTx G.x G.ε) = _
    unfold bTx
    rw [Real.log_exp]
  refine ⟨hL, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · rw [hL]; rfl
  · have h1 : (Fintype.card (E0 × H) : ℂ) = 2 * ((PhiSet (H := H)).card : ℂ) := Formalism.D5.Bal.card_G_eq
    have h2 : Fintype.card (E0 × H) = 2 * (PhiSet (H := H)).card := by exact_mod_cast h1
    have h3 : Fintype.card (E0 × H) = 4 * Fintype.card H := by
      simp [Fintype.card_prod]
    have h4 : (PhiSet (H := H)).card = 2 * Fintype.card H := by omega
    exact_mod_cast h4
  · intro hx hk
    show 0 ≤ (T2.card : ℝ) * G.k * bTx G.x G.ε * G.x ^ G.ε
      / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * G.x ^ (-G.ε)))
    have hb : 0 ≤ bTx G.x G.ε := (Real.exp_pos _).le
    exact div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hk) hb) (Real.rpow_nonneg hx _))
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hx _)))
  · show (Fintype.card TT : ℝ) = _
    rw [Fintype.card_coe]

theorem exponent_comparison_of_constant : TypePrimeCostOfDeviationBound := by
  intro U0 W Top _ m f D C C0 Pl e aP sE haP hE hC hB h
  have hsum : (∑ t ∈ Finset.univ.map e, aP t) = D.sumA := by
    rw [Finset.sum_map]
    simp only [haP]
    rfl
  constructor
  · intro u0 u j
    have h1 := (h u0 u).1 j
    rw [hsum] at h1
    rw [hE u0 u j]
    exact h1.trans (mul_le_mul_of_nonneg_right hC hB)
  · intro u0 u
    have h1 := (h u0 u).2
    rw [hsum] at h1
    have e1 : D.Ee u0 u = 2 * ∑ j, sE u0 u j := by
      unfold Data.Ee
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => hE u0 u j
    rw [e1]
    have e2 : (m : ℝ) * D.sumA * D.lg = (m : ℝ) * (D.sumA * D.lg) := by ring
    rw [e2]
    have hmB : 0 ≤ (m : ℝ) * D.B0 := mul_nonneg (Nat.cast_nonneg _) hB
    calc _ ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * ((m : ℝ) * D.B0) := h1
      _ ≤ C.cE * ((m : ℝ) * D.B0) := mul_le_mul_of_nonneg_right hC hmB
      _ = C.cE * (m : ℝ) * D.B0 := by ring

theorem height_comparison_of_constant : HeightVariationOfCorrectedHeightBound := by
  intro U0 W Top _ m f D C C0 Pl e aP haP hC ha hLa hB h u0 u u'
  have h1 := h u0 u u'
  rw [Finset.sum_map, Finset.sum_map, Finset.card_map, Finset.card_univ] at h1
  simp only [haP] at h1
  have hX : 0 ≤ (Fintype.card Top : ℝ) * D.a * D.La + (m : ℝ) * D.B0 :=
    add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ha) hLa) (mul_nonneg (Nat.cast_nonneg _) hB)
  exact h1.trans (mul_le_mul_of_nonneg_right hC hX)




lemma ne_bot_of_span {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [Nonempty ι]
    (b : Basis ι K V) (A : Submodule (𝓞 K) V) (hsp : Submodule.span K (A : Set V) = ⊤) : A ≠ ⊥ := by
  rintro rfl
  have h0 : Submodule.span K (((⊥ : Submodule (𝓞 K) V) : Set V)) = ⊥ := by simp
  rw [h0] at hsp
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have : b i ∈ (⊥ : Submodule K V) := by rw [hsp]; trivial
  exact b.ne_zero i (by simpa using this)

theorem dual_slopes : DualSlopes := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ _ b X hX A hA hsp
  obtain ⟨dfg, dsp, _, dsize, dleast, dlargest, _⟩ := dual_polygon_identity K V ι b X hX A hA hsp
  have hX' := Formalism.HN.DualPolygon.dualFrame_unit X hX
  have hA0 : A ≠ ⊥ := ne_bot_of_span b A hsp
  have hD0 : dualLat A ≠ ⊥ := ne_bot_of_span b.dualBasis (dualLat A) dsp
  obtain ⟨_, a2, _, a4, a5, _⟩ := size_maximal_slope K V ι b X hX A hA hA0
  obtain ⟨_, d2, _, d4, d5, _⟩ :=
    size_maximal_slope K (Module.Dual K V) ι b.dualBasis (dualFrame X) hX' (dualLat A) dfg hD0
  refine ⟨?_, ?_, ?_⟩
  · rw [d2, a2, dsize, Real.log_inv]
    ring
  · rw [d5, a4, ← Real.exp_neg] at dlargest
    have h := Real.exp_injective dlargest
    unfold muMinDef muMaxDef
    have e : logDisc K / (2 * (Module.finrank ℚ K : ℝ)) = logDisc K / (Module.finrank ℚ K : ℝ) / 2 := by ring
    rw [e] at h
    linarith
  · rw [d4, a5, ← Real.exp_neg] at dleast
    have h := Real.exp_injective dleast
    unfold muMinDef muMaxDef
    have e : logDisc K / (2 * (Module.finrank ℚ K : ℝ)) = logDisc K / (Module.finrank ℚ K : ℝ) / 2 := by ring
    rw [e] at h
    linarith

theorem mu_log_conductor : MuLcv := by
  intro K _ _ _ _ D hD X hX R hR
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hR0 : R ≠ ⊥ := ne_bot_of_span (Pi.basisFun K (Fin D)) R hR.span_eq_top
  obtain ⟨_, a2, _⟩ := size_maximal_slope K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hR.fg hR0
  have hpos : 0 < ht (Pi.basisFun K (Fin D)) X R :=
    (place_lattice_structure K _ (Fin D) (Pi.basisFun K (Fin D)) X hX R hR.fg).2.2
  have hrk : rkK R = D := by
    unfold rkK
    rw [hR.span_eq_top, finrank_top]
    simp
  have hn : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
    have := sizeMu_finrank_eq K
    exact_mod_cast this
  rw [a2]
  unfold size lcv
  rw [Real.log_rpow hpos, hrk, hn]
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hnp : (nPl K : ℝ) ≠ 0 := by
    have h1 : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
    intro h0
    rw [hn, h0] at h1
    simp at h1
  field_simp

theorem mu_constant_of_blocks : MuCCOfRows := by
  intro I m F D hD XE hXE hX' R hR ψ hψ
  obtain ⟨hinj, hnorm, hcc⟩ := hψ
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  obtain ⟨dfg, _⟩ := dual_polygon_identity F.K (Fin D → F.K) (Fin D) (Pi.basisFun F.K (Fin D)) XE hXE R hR.fg
    hR.span_eq_top
  obtain ⟨_, _, r3, _, r5, _⟩ := lattice_rerealization F.K (Module.Dual F.K (Fin D → F.K)) (Fin D) F.Wd F.κ
    (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) F.b' F.X' ψ (Formalism.HN.DualPolygon.dualFrame_unit XE hXE) hX' hinj hnorm
    (dualLat R) dfg
  obtain ⟨s1, s2, _⟩ := dual_slopes F.K (Fin D → F.K) (Fin D) (Pi.basisFun F.K (Fin D)) XE hXE R hR.fg
    hR.span_eq_top
  have m1 := mu_log_conductor F.K D hD XE hXE R hR
  constructor
  · rw [hcc]
    have : muDef F.b' F.X' ((dualLat R).map (ψ.restrictScalars (𝓞 F.K)))
        = muDef (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) (dualLat R) := by
      unfold muDef
      rw [r3]
    rw [this, s1, m1]
    ring
  · rw [hcc]
    have : muMinDef F.b' F.X' ((dualLat R).map (ψ.restrictScalars (𝓞 F.K)))
        = muMinDef (Pi.basisFun F.K (Fin D)).dualBasis (dualFrame XE) (dualLat R) := by
      unfold muMinDef
      rw [r5]
    rw [this, s2]

lemma plOf_bijective (K : Type) [Field K] [NumberField K] :
    Function.Bijective (plOf : HeightOneSpectrum (𝓞 K) → slopeLatticeData.FinPl K) := by
  constructor
  · intro w w' h
    have : w.asIdeal = w'.asIdeal := congrArg Subtype.val h
    exact HeightOneSpectrum.ext this
  · intro p
    refine ⟨⟨p.1, p.2.isPrime, ?_⟩, rfl⟩
    exact Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)

theorem sum_over_places : SumOverPlaces := by
  intro K _ _ S φ
  have hb := plOf_bijective K
  constructor
  · refine (S.finite_toSet.preimage hb.1.injOn).subset ?_
    intro w hw
    by_contra hn
    apply hw
    have : plOf w ∉ S := hn
    simp [this]
  · set g : slopeLatticeData.FinPl K → ℝ := fun v => slopeLatticeData.ell v * (if v ∈ S then ramE v * φ v else 0) with hg
    have h1 : (∑ᶠ w : HeightOneSpectrum (𝓞 K),
        lw w * (if plOf w ∈ S then ramE (plOf w) * φ (plOf w) else 0)) = ∑ᶠ v, g v :=
      finsum_comp_equiv (Equiv.ofBijective plOf hb) (f := g)
    rw [h1, finsum_eq_sum_of_support_subset (s := S)]
    · refine Finset.sum_congr rfl fun w hw => ?_
      simp only [hg, hw, if_true, lE]
      ring
    · intro v hv
      by_contra hn
      apply hv
      have : v ∉ S := hn
      simp [hg, this]

theorem function_of_places : FoOfPlaces := by
  intro I m F
  show 2 * ∑ j ∈ Finset.univ, ∑ w ∈ F.S, lE w * F.Fj j w = _
  congr 1
  exact Finset.sum_congr rfl fun j _ => (sum_over_places F.K F.S (F.Fj j)).2

theorem exponent_of_places : EeJOfPlaces := by
  intro I m F u j
  show 2 * ∑ w ∈ F.S, lE w * F.Ej u j w = _
  congr 1
  exact (sum_over_places F.K F.S (F.Ej u j)).2


theorem divisibility_free_at : DivFreeIsDivAt := by
  intro U0 W Top _ m f D C logOm
  exact Iff.rfl


theorem construct_divisibility_of_conclusion : MkDivOfConcl := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm logOm C0 Dd XE R ψ hD hXE hX' hR hψ hC hx hk hLa h u0 u
  have h1 := h u0 u
  unfold ThmConcl at h1
  rw [Finset.sum_map, Finset.card_map] at h1
  have hmu := (mu_constant_of_blocks (W u0) m (Fm u0) (Dd u0) (hD u0) (XE u0) (hXE u0) (hX' u0) (R u0) (hR u0)
    (ψ u0) (hψ u0)).1
  have hFo := function_of_places (W u0) m (Fm u0)
  rw [← hmu, ← hFo] at h1
  have hNc : 0 ≤ (mkData G C.cHH D ell N TT T2 a w Fm).Nc :=
    (construct_parameter_definitions H W m G C.cHH D ell N TT T2 a w Fm).2.2.2.2.2.1 hx hk
  set Nc := (mkData G C.cHH D ell N TT T2 a w Fm).Nc with hNcdef
  show muDef (Fm u0).b' (Fm u0).X' (Fm u0).cc + (Fm u0).h u - (Fm u0).Fo ≤
    (∑ t : TT, ((m : ℝ) * (ph (a t) - a t * logOm) - a t * Real.log ((Fm u0).T u : ℝ)))
      + C.cDiv * (Fintype.card TT : ℝ) * (G.x * Real.exp (G.x ^ G.ε)) * G.La
      + C.cDiv * (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * Real.exp (G.x ^ G.ε) * G.x ^ G.ε + Nc)
        * G.x ^ (C.eDiv * G.ε)
  rw [Finset.sum_coe_sort TT
    (fun t => (m : ℝ) * (ph (a t) - a t * logOm) - a t * Real.log ((Fm u0).T u : ℝ)), Fintype.card_coe]
  have hsum : (∑ t ∈ TT, ((m : ℝ) * (Formalism.LatticeIndexTer.ph ((fun ρ : E0 × H => a ρ.2) (topEmb H t))
        - (fun ρ : E0 × H => a ρ.2) (topEmb H t) * logOm)
        - (fun ρ : E0 × H => a ρ.2) (topEmb H t) * Real.log ((Fm u0).T u : ℝ)))
      = ∑ t ∈ TT, ((m : ℝ) * (ph (a t) - a t * logOm) - a t * Real.log ((Fm u0).T u : ℝ)) := rfl
  rw [hsum] at h1
  have he : 0 ≤ Real.exp (G.x ^ G.ε) := (Real.exp_pos _).le
  have hX : 0 ≤ (TT.card : ℝ) * (G.x * Real.exp (G.x ^ G.ε)) * G.La :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hx he)) hLa
  have hB : 0 ≤ (2 * (Fintype.card H : ℝ)) * m * Real.exp (G.x ^ G.ε) * G.x ^ G.ε :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) he)
      (Real.rpow_nonneg hx _)
  have hY : 0 ≤ (m : ℝ) * ((2 * (Fintype.card H : ℝ)) * m * Real.exp (G.x ^ G.ε) * G.x ^ G.ε + Nc)
      * G.x ^ (C.eDiv * G.ε) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hB hNc)) (Real.rpow_nonneg hx _)
  have h2 := mul_le_mul_of_nonneg_right hC (add_nonneg hX hY)
  nlinarith [h1, h2]

lemma univ_map_top {H : Type} [AddCommGroup H] (TT : Finset H) :
    (Finset.univ : Finset TT).map ((Function.Embedding.subtype _).trans (topEmb H)) = TT.map (topEmb H) := by
  rw [← Finset.map_map, Finset.univ_eq_attach, Finset.attach_map_val]

lemma threshold_constant_nonneg {H : Type} [Fintype H] (m : ℕ) (x ε : ℝ) (hx : 0 ≤ x) :
    0 ≤ (2 * (Fintype.card H : ℝ)) * (m : ℝ) * Real.exp (x ^ ε) * x ^ ε :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (Real.exp_pos _).le) (Real.rpow_nonneg hx _)

theorem construct_exponent_comparison : TypePrimeCostOfDeviationBoundArith := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm C0 g hg hC hx h
  refine exponent_comparison_of_constant H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C C0 (E0 × H)
    ((Function.Embedding.subtype _).trans (topEmb H)) (fun ρ => a ρ.2)
    (fun u0 u j => ∑ᶠ z : HeightOneSpectrum (𝓞 (Fm u0).K),
        lw z * (if plOf z ∈ (Fm u0).S then ramE (plOf z) * (Fm u0).Ej u j (plOf z) else 0))
    (fun t => rfl) (fun u0 u j => exponent_of_places (W u0) m (Fm u0) u j) hC
    (threshold_constant_nonneg (H := H) m G.x G.ε hx) ?_
  intro u0 u
  rw [univ_map_top]
  have h1 := h u0 u
  rw [← hg] at h1
  exact h1

theorem construct_height_comparison : HeightVariationOfCorrectedHeightBoundArith := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm C0 hC hx hLa h
  refine height_comparison_of_constant H W TT m _ (mkData G C.cHH D ell N TT T2 a w Fm) C C0 (E0 × H)
    ((Function.Embedding.subtype _).trans (topEmb H)) (fun ρ => a ρ.2) (fun t => rfl) hC
    (mul_nonneg hx (Real.exp_pos _).le) hLa (threshold_constant_nonneg (H := H) m G.x G.ε hx) ?_
  intro u0
  rw [univ_map_top]
  exact h u0

theorem construct_height_bound : MkHHOfFun := by
  intro H _ _ _ W _ m G C D ell N TT T2 a w Fm Dd XE R ψ hD hXE hX' hR hψ h u0
  have hmu := (mu_constant_of_blocks (W u0) m (Fm u0) (Dd u0) (hD u0) (XE u0) (hXE u0) (hX' u0) (R u0) (hR u0)
    (ψ u0) (hψ u0)).2
  have h1 := h u0
  rw [hmu]
  linarith

def satD : Data Unit (fun _ => Unit) (Fin 1) 1 1 where
  x := 1
  ε := 1 / 52
  a := Real.exp 1
  b := Real.exp 1
  b' := 1
  k := 1
  L := 1
  La := 1
  B0 := Real.exp 1
  Nc := 0
  gam := 0
  LpL := 0
  v := Real.pi * Real.exp (-1)
  lg := 0
  logGam := 0
  aT := fun _ => 0
  w := fun _ _ _ => 1
  d := fun _ _ => 1
  T := fun _ _ => 1
  muN := fun _ _ => 0
  muMaxN := fun _ _ => 0
  h := fun _ _ => 4
  muM := fun _ _ => 0
  muMaxM := fun _ _ => 0
  EeJ := fun _ _ _ => 0
  muCC := fun _ => 3 + Real.exp 1
  muMinCC := fun _ => 0
  Fo := fun _ => 0
  Ga := fun _ => 0
  Ta := fun _ => 0
  ASK := fun _ => 0
  IO := fun _ => 0
  HH := fun _ => 1
  del := fun _ => 0
  η := fun _ => 0
  e := fun _ => 0
  delBar := 0
  etaBar := 0
  eBar := 0

def satC : Consts where
  cDiv := 60
  eDiv := 1
  cE := 0
  cH := 0
  cCount := 0
  cSlope := 0
  cSl1 := 0
  cLoss := 0
  eLoss := 0
  cHH := 0

def satP : ParNums where
  rd := 1
  f := 1
  N := 1
  S := 0
  tt := 0
  η := 0
  w'' := 0
  dC := 1
  lam0 := 1
  C0 := 1

def satSt : StepNums (Fin 1) (Fin 1) where
  mu0 := 1 + Real.exp 1
  FoP := 0
  hP := 2
  mlam := -1
  hK := fun _ => 1
  phν := fun _ _ => 2
  nν := fun _ _ => 4
  fa := fun _ _ => 0
  Lpass := 2
  Eb := Real.exp 1
  e6 := 1
  eP := 2
  eK := fun _ => 3
  pq := fun _ => 1
  w := fun _ _ => 1
  eE := fun _ _ => 2
  δ := fun _ _ => 3


end Formalism.LFunctionChainParameters.LBrDiv
