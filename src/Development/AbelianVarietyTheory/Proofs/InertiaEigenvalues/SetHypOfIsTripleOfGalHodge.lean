import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnramifiedNoJump
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BoundedDenominatorsOfBeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactorsStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassTermBoundBetaOfToricDenominator

section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTieWeak

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem isThEmpty_of_isThOf {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ}
    {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF D.host.E)} {χ : Formalism.L2.Host.HChar D.host.E}
    (h : IsThOf X i ι lam φ s κ 𝔣 χ) : IsThEmpty X i ι lam φ s κ 𝔣 χ := by
  classical
  obtain ⟨u, hu, hth⟩ := h
  have hQ : BlochKatoReduction.Gen.QOk X i ∅ :=
    ⟨fun _ h => absurd h (Finset.notMem_empty _), Finset.disjoint_empty_left _, fun _ h => absurd h (Finset.notMem_empty _)⟩
  obtain ⟨hfin, π, T, -, hT, hδ⟩ := hth ∅ hQ
  have he : belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))) = ∅ := Finset.image_empty _
  have hc : condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E)))) = 𝔣 := by
    rw [he]; simp [condQ]
  have := Fintype.ofFinite (PicO (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))))
  have t : IsToricSum φ s κ (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))) χ (∑ q, T q) :=
    (isToricSum_iff _ _ _ _ _ _).2 ⟨hfin, T, hT, (finsum_eq_sum_of_fintype _).symm⟩
  have key : ∀ z : ℂ, IsToricSum φ s κ (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))) χ z →
      IsToricSum φ s κ 𝔣 χ z := by
    rw [hc]; exact fun _ hz => hz
  refine ⟨u, ∑ q, T q, hu, key _ t, ?_⟩
  rw [map_sum, Finset.sum_congr rfl fun δ _ => hδ δ, ← Finset.mul_sum, ← map_sum,
    ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹)]
  congr 2
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset]

theorem isLamTie0_of_isLamTie : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D),
    IsLamTie X Z → IsLamTie0 X Z := by
  intro D N X Z h i hi lam
  obtain ⟨-, ι, -, hι⟩ := h i hi
  obtain ⟨j, a, s, hl, ht⟩ := hι lam
  exact ⟨_, j, a, s, hl.2.1, isThEmpty_of_isThOf ht⟩

end GlobalTheory.LamTieWeak
end
end

section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricDistribution

namespace GlobalTheory.ToricAssembly

theorem toricSumFormula : ToricSumFormula :=
  GlobalTheory.T.toric_sum_eq_hecke_L_value_mul_auxiliary_factors exists_isHeckeL_of_hasInf

theorem not_isNormPow {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ}
    {𝔣 : Ideal (OF E)} {χ : HChar E} (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ) :
    ¬ ∃ t : ℝ, GlobalTheory.HeckeOne.IsNormPow χ t := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hb.2.1
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, fun h => hb.1 (le_bot_iff.1 (h ▸ hle))⟩
  have hv : v.asIdeal ∣ 𝔣 := Ideal.dvd_iff_le.2 hle
  obtain ⟨P, -, -, hP, -⟩ := (hb.2.2 v hv).1
  exact GlobalTheory.HeckeOne.not_isNormPow_of_not_unrAt
    (((hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)).not_unrAt (multiplicity_ne_zero.2 hv))

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem qOk_empty (i : X.Tw) : BlochKatoReduction.Gen.QOk X i ∅ :=
  ⟨fun _ h => absurd h (Finset.notMem_empty _), Finset.disjoint_empty_left _, fun _ h => absurd h (Finset.notMem_empty _)⟩

theorem sum_ne_zero_at (hL : ToricSumFormula) {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {s : ℕ}
    (ht : IsToricEltAt X i ι lam s) : ∑ δ, X.th i ∅ lam δ ≠ 0 := by
  classical
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨I, _, φ, κ, 𝔣, χ, u, hD, h𝔣, -, hu, hth⟩ := ht
  obtain ⟨hfin, π, T, -, hT, hδ⟩ := hth ∅ (qOk_empty i)
  have he : belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))) = ∅ := Finset.image_empty _
  obtain ⟨hφ, -, hs, -, hb, hχ⟩ := hD
  have hn := not_isNormPow hb hχ
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 hn
  have h0 : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hχ.1 hn hΛ (by exact_mod_cast hs)
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 D.host.E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := hL _ I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ host_unramFin hs hb (fun _ h => absurd h (Finset.notMem_empty _)) hχ
    (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one, ← he] at t1
  have := Fintype.ofFinite (PicO (condQ 𝔣 (belowSet ∅)))
  have e : Λ s = ∑ q, T q :=
    t1.unique ((isToricSum_iff _ _ _ _ _ _).2 ⟨hfin, T, hT, (finsum_eq_sum_of_fintype _).symm⟩)
  intro hz
  have h1 := congrArg (algebraMap (FractionRing (X.O i)) (Kbar X i)) hz
  rw [map_sum, map_zero, Finset.sum_congr rfl fun δ _ => hδ δ, ← Finset.mul_sum, ← map_sum] at h1
  refine mul_ne_zero hu ((map_ne_zero ι).2 ?_) h1
  rw [e, ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹)] at h0
  convert h0 using 2 with δ
  rw [show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset]

theorem gen_sum_ne_zero (hL : ToricSumFormula) (ht : IsToricElt X) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (lam : X.abelian₂ i)
    (hs : ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s) : ∑ δ, X.th i ∅ lam δ ≠ 0 := by
  obtain ⟨s, hs⟩ := hs
  obtain ⟨s, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans zero_le_one hs.2.1)
  obtain ⟨ι, -, hι⟩ := ht i hi
  exact sum_ne_zero_at hL (hι lam s hs)

theorem gen_toric_properties (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hL : ToricSumFormula) (hB : ClassTermBound)
    (ht : IsToricElt X) :
    ∃ N0 : X.Tw → ℕ, BlochKatoReduction.Gen.adm9 X N0 ∧ BlochKatoReduction.Gen.adm10 X ∧
      ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, (∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s) → ∑ δ, X.th i ∅ lam δ ≠ 0 := by
  obtain ⟨N0, h⟩ := exists_gen_bound X hB ht
  exact ⟨N0, h, gen_relation hA hL ht, gen_sum_ne_zero hL ht⟩

end Record

theorem toric_properties_of_bound (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hB : ClassTermBound) (D : D7)
    (ht : IsToricElt D.ntw) :
    ∃ N0 : D.ntw.Tw → ℕ, BlochKatoReduction.adm9 D N0 ∧ BlochKatoReduction.adm10 D ∧
      ∀ i, D.ntw.NonzeroIndexPlace i → ∀ lam : D.ntw.abelian₂ i, (∃ s : ℤ, BlochKatoReduction.Gen.SOk D.ntw i lam s) → ∑ δ, D.ntw.th i ∅ lam δ ≠ 0 :=
  gen_toric_properties hA toricSumFormula hB ht

theorem toric_properties (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hB : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator) (D : D7)
    (ht : IsToricElt D.ntw) :
    ∃ N0 : D.ntw.Tw → ℕ, BlochKatoReduction.adm9 D N0 ∧ BlochKatoReduction.adm10 D ∧
      ∀ i, D.ntw.NonzeroIndexPlace i → ∀ lam : D.ntw.abelian₂ i, (∃ s : ℤ, BlochKatoReduction.Gen.SOk D.ntw i lam s) → ∑ δ, D.ntw.th i ∅ lam δ ≠ 0 :=
  toric_properties_of_bound hA (GlobalTheory.ToricDenomBridge.classTermBound_of_toricDenominator hB) D ht

end GlobalTheory.ToricAssembly
end
end

section
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.ToricValue

theorem exists_heckeL_toricSum : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : Formalism.L2.Host.HChar H.E), IsHostDatum H φ s κ 𝔣 χ → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ s ≠ 0 ∧ ∀ T : ℂ, IsToricSum φ s κ 𝔣 χ T ↔ T = Λ s := by
  intro R H I _ φ s κ 𝔣 χ hD
  have : IsCMField H.E := H.isCMField_hostE
  obtain ⟨hφ, -, hs, -, hb, hχ⟩ := hD
  have hn := GlobalTheory.ToricAssembly.not_isNormPow hb hχ
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.HeckeOne.entire_of_not_normPow hχ.1 hn
  have h0 : Λ s ≠ 0 := GlobalTheory.HeckePartial.IsHeckeL.ne_zero_of_one_le hχ.1 hn hΛ (by exact_mod_cast hs)
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 H.E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 H.E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricAssembly.toricSumFormula _ I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ (GlobalTheory.ToricDenomBridge.host_unramFin H) hs hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one] at t1
  have e : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  rw [e] at t1
  exact ⟨Λ, hΛ, h0, fun T => ⟨fun h => h.unique t1, fun h => h ▸ t1⟩⟩

end GlobalTheory.ToricValue
end
end

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeL_eq_toricSum_ne_zero : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E)) (χ : Formalism.L2.Host.HChar H.E), IsHostDatum H φ s κ 𝔣 χ → ∃ Λ : ℂ → ℂ, IsHeckeL χ Λ ∧ Λ s ≠ 0 ∧ ∀ T : ℂ, IsToricSum φ s κ 𝔣 χ T ↔ T = Λ s := by
  atlas_forward_decl GlobalTheory.ToricValue.exists_heckeL_toricSum
end

section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem sum_th_empty_ne_zero : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D), Z.Ok → IsLamTie0 X Z → ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, (∑ δ, X.th i ∅ lam δ) ≠ 0 ∧ ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s := by
  intro D N X Z hZ hT i hi lam
  obtain ⟨ι, j, a, s, hs, u, T, hu, hTs, hEq⟩ := hT i hi lam
  refine ⟨?_, s, hs⟩
  have h1 : 1 ≤ s := by
    have := hs.2.1
    exact_mod_cast this
  have h2 : (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 := hs.2.2
  obtain ⟨Λ, -, hne, hiff⟩ := GlobalTheory.T.exists_heckeL_eq_toricSum_ne_zero D.R D.host _ (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0)
    (Z.lam0 (X.l i) j a) (GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (X.l i) j a s h1 h2)
  have hT0 : T ≠ 0 := by rw [(hiff T).1 hTs]; exact hne
  intro h0
  rw [h0, map_zero] at hEq
  exact mul_ne_zero hu ((map_ne_zero ι).2 hT0) hEq.symm

end GlobalTheory.LamTie
end

section
noncomputable section

namespace GlobalTheory.SettingHypotheses

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem setHyp_of_isTriple_of_galHodge (hC : GlobalTheory.Published.ChebotarevDegreeOne) (D : D7)
    (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (C₀ : Formalism.L2.Host.CharFrame D) (S : GlobalTheory.HeightCounting.CharSide D C₀)
    (hG : GlobalTheory.TripleLocal.GalHodge D T) (h2 : Formalism.MainNotions.BlochKatoReduction.adm2 D) (h : GlobalTheory.Triple.IsTriple D)
    (Z : GlobalTheory.LamTie.LamDat D) (hZ : Z.Ok) (hL : GlobalTheory.LamTie.IsLamTie D.ntw Z)
    (hr : 100 ≤ D.R.r) (hg : ∀ k, 2 * D.R.r ≤ D.host.g k) :
    ∀ i, D.ntw.NonzeroIndexPlace i → SetHyp (bk0 D) i := fun i hi =>
  have hA := (GlobalTheory.TripleLocal.galois_hypotheses_of_isTriple S
    (GlobalTheory.SplitFrobDense.frobDense D (GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 hC)) hG h2 h).2.2 i hi
  have hT := GlobalTheory.LamTie.sum_th_empty_ne_zero D D.nd D.ntw Z hZ
    (GlobalTheory.LamTieWeak.isLamTie0_of_isLamTie D D.nd D.ntw Z hL) i hi
  ⟨hA.1, fun s _ => (hA.2 s).1, fun s _ => (hA.2 s).2, fun lam => (hT lam).1, fun lam => (hT lam).2, hr, hg⟩

end GlobalTheory.SettingHypotheses
end
end
