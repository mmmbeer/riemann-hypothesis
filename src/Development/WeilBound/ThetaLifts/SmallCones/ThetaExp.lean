import Development.WeilBound.ThetaLifts.SmallCones.ThetaKernelGeneralIdentity
import Development.WeilBound.ThetaLifts.SmallCones.GenSmallOf
import Development.WeilBound.ThetaLifts.SmallCones.Kernel
import Development.WeilBound.ThetaLifts.SmallCones.KerPol
import Development.WeilBound.ThetaLifts.SmallCones.ConeBasic
import Development.WeilBound.ThetaLifts.SmallCones.SliceAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
import Development.WeilBound.ThetaLifts.SmallCones.LineInt
import Mathlib
import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.TateAbs
import Development.WeilBound.ThetaLifts.SmallCones.Unfold
import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.IsFrPlane
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorIdeleNormalizedAbsIdeleHalfAtInfinity
import Development.WeilBound.ThetaLifts.TowerModels.PlaneReal
import Development.WeilBound.ThetaLifts.TowerModels.PlaneMain
import Development.WeilBound.ThetaLifts.TowerModels.ExistsRefl
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerProd
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.MemLatWIff
import Development.WeilBound.ThetaLifts.SmallCones.KFinDataOf
import Development.WeilBound.ThetaLifts.SmallCones.FormSwapZero
import Development.WeilBound.ThetaLifts.SmallCones.LinExOf
import Development.WeilBound.ThetaLifts.SmallCones.SoZero

section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lawα {n d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {χ χ' : Chr F E} {x y : ℝ} {T : UA σ W.J → ℂ}
    (_n : n = n) (h : HasLaw W₁ H' χ x T) (e1 : χ = χ') (e2 : x = y) : HasLaw W₁ H' χ' y T := by subst e1 e2; exact h

theorem splitEx_of (hB : GenBig) (hSm : GenSmall) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx)
    (hPl : PlaneHerm) (hC : EvCone) (hZ : EvZero) (hU : UnipEx) (hL : Low) (hT : TriplePair) : SplitEx := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h d₁ W₁ H' i₀ i₁ hH'
  obtain ⟨hp, hp', hw⟩ := hT F E σ B a a' G X om om' h
  obtain ⟨h1, h2, hW₁⟩ := (hL F E σ B _ _ G.W W₁ H' i₀ i₁ _ _ h.base hH').2 h.geo.hW
  have hlt := h.geo.lt
  have hev := h.geo.even
  have heB := h.geo.eBig
  have haB := h.geo.aBig
  obtain ⟨k, hk⟩ := hev
  have uniq : ∀ f fa fb, Split2 W₁ H' X f fa fb → ∃! x : (UA σ G.W.J → ℂ) × (UA σ G.W.J → ℂ), Split2 W₁ H' X f x.1 x.2 :=
    fun f fa fb hs => ⟨(fa, fb), hs, fun y hy => Prod.ext (split_uniq hU h hH' hy hs).1 (split_uniq hU h hH' hy hs).2⟩
  refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
  · obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h.base _ _ G.V W₁ _ _ _ _ h.geo.hV hW₁
    obtain ⟨om₁, hp₁⟩ := hW _ _ hp.hX hp.hW hp.resX (res_low hp.resW hH'.rank) M₁ hM₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hp d₁ G.V W₁ H' i₀ i₁ M₁ rfl hH' hM₁
    obtain ⟨C₀, -, H0⟩ := anyBig hB hA hK hS hI hP hPl hC F E σ B a (a + a') d₁ G.V G.W W₁ H' i₀ i₁ (a - G.p) G.p _ _ G.M M₁
      (by omega) ⟨(a - a') / 2, by omega, by omega⟩ hH' e₀ he₀
    obtain ⟨A₀, A₁, c1, c2, c3, -⟩ := H0 _ _ om om₁ (IsPair.cast hp rfl rfl (by omega) (by omega)) hp₁ Φ hΦ (by simp)
    exact uniq _ A₁ A₀ ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  · obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h.base _ _ G.V' W₁ _ _ _ _ h.geo.hV' hW₁
    obtain ⟨om₁, hp₁⟩ := hW _ _ hp'.hX hp'.hW hp'.resX (res_low hp'.resW hH'.rank) M₁ hM₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp' d₁ G.V' W₁ H' i₀ i₁ M₁ rfl hH' hM₁
    obtain ⟨C₀, -, H0⟩ := anySmall hSm hA hK hS hI hP hPl hC F E σ B a' (a + a') d₁ G.V' G.W W₁ H' i₀ i₁ G.q (a' - G.q) _ _ G.M' M₁
      (by omega) ⟨(a - a') / 2 + 1, by omega, by omega⟩ hH' e₀ he₀
    obtain ⟨A₀, A₁, c1, c2, c3, -⟩ := H0 _ _ om' om₁ (IsPair.cast hp' rfl rfl (by omega) (by omega)) hp₁ Φ hΦ.1 (fun _ => hΦ.2)
    exact uniq _ A₀ A₁ ⟨c1, c2, lawα (n := 0) rfl c3 (by simp) (by push_cast; ring)⟩

theorem ctBigZero_of (hB : GenBig) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx)
    (hPl : PlaneHerm) (hC : EvCone) (hU : UnipEx) (hT : TriplePair) : CTBigZero := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e he
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  obtain ⟨eV, ep, eq, hH, hH'⟩ := hc
  dsimp only at eV ep eq hH hH' he
  subst eV ep
  by_cases hex : ∃ X om om', IsTriple B G X om om'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' _ _ h => absurd ⟨X, om, om', h⟩ hex⟩
  obtain ⟨X0, o, o', h0⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨C₀, hC₀, H0⟩ := anyBig hB hA hK hS hI hP hPl hC F E σ B a (a + (b + 2)) (a + b) G.V G.W W₁ H' _ _ (a - G.p) G.p
    (a + b - (G.p + q₁)) (G.p + q₁) G.M M₁ (by omega) ⟨(a - (b + 2)) / 2, by omega, by omega⟩ hH' e he
  refine ⟨C₀, hC₀, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₁ (IsPair.cast (hT F E σ B _ _ G X om om' h).1 rfl rfl (by omega) (by omega))
    (hT F E σ B _ _ _ X om₁ om₁' h₁).1 Φ hΦ (by simp)
  have := split_uniq hU h hH' hs (fa' := A₁) (fb' := A₀)
    ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  rw [this.2]
  exact c4 g m hm x (by simp)

theorem ctSmallZero_of (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hT : TriplePair) : CTSmallZero := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he
  obtain ⟨C, hC, H0⟩ := hA F E σ B a' _ _ G.V' G.W G₁.W H' _ _ G.q (a' - G.q) (b + 2 + a' - (G.p + G.q)) (G.p + G.q)
    (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) G₁.V' G.M' G₁.M' hc.eV (by rw [hc.q0]; simp) hc.hH' e he
  refine ⟨C, hC, fun X om om' om₁ om₁' h h₁ Φ hΦ => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).2.1
  obtain ⟨K, μK, μ, hK1, -⟩ := hS F E σ B _ G.V' _ _ h.base hp.herm
  obtain ⟨A₀, c1, c2, c3⟩ := H0 _ _ om' om₁' hp
    (IsPair.cast (hT F E σ B _ _ G₁ X om₁ om₁' h₁).2.1 (by rw [hc.q0, hc.q1]) (by rw [hc.q0, hc.q1]) rfl rfl) Φ
    (hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ).1
  exact ⟨A₀, ⟨by rwa [add_zero], c2, fun t m _ h => by simp⟩, c3⟩

theorem ctBigCone_of (hB : GenBig) (hK : KFinData) (hI : IwaEx) (hP : PairEx) (hZ : EvZero) (hU : UnipEx) (hT : TriplePair) :
    CTBigCone := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he K μK μ hK1 hμK hμ
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' h h₁ => absurd ⟨X, om, om', om₁, om₁', h, h₁⟩ hex⟩
  obtain ⟨X0, o, o', o₁, o₁', h0, h1⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  have e1 := hc.ep
  have e2 := hc.q0
  have e3 := hc.q1
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h0.base _ _ G.V G₁.W _ _ _ _ h0.geo.hV h1.geo.hW
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ o _ _ _ _ (hT F E σ B _ _ G X0 o o' h0).1 _ G.V G₁.W H' _ _ M₁ rfl hc.hH' hM₁
  obtain ⟨C₀, C₁, -, hC₁, H0⟩ := hB F E σ B _ _ _ _ G.V G.W G₁.V G₁.W H H' _ _ _ _ (b - G₁.p) G₁.p (b + a' - (G₁.p + G₁.q))
    (G₁.p + G₁.q) G.M G₁.M hc.hH hc.hH' M₁ e₀ e hM₁ h1.geo.hM he₀ he ((b + 2 - a') / 2) ⟨by omega, by omega⟩ K μK μ
    (hI F E σ B _ _ G.V _ _ H h0.base h0.geo.hV (adapted_x_ne hc.hH) hc.hH.xx K hK1) hμK hμ
  refine ⟨C₁, hC₁, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).1
  have hp₁ := (hT F E σ B _ _ G₁ X om₁ om₁' h₁).1
  obtain ⟨om₂, hp₂⟩ := hW _ _ hp.hX hp.hW hp.resX hp₁.resW M₁ hM₁
  obtain ⟨hs1, hf⟩ := hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₂ om₁ (IsPair.cast hp (by omega) (by omega) (by omega) (by omega))
    (IsPair.cast hp₂ (by omega) (by omega) rfl rfl) hp₁ Φ hs1 hf
  have := split_uniq hU h hc.hH' hs (fa' := A₁) (fb' := A₀)
    ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  rw [this.1, (c4 g m hm x).1, inv_div]
  rfl

theorem ctSmallCone_of (hB : GenSmall) (hK : KFinData) (hI : IwaEx) (hP : PairEx) (hZ : EvZero) (hU : UnipEx) (hT : TriplePair) :
    CTSmallCone := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e he K μK μ hK1 hμK hμ
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' h h₁ => absurd ⟨X, om, om', om₁, om₁', h, h₁⟩ hex⟩
  obtain ⟨X0, o, o', o₁, o₁', h0, h1⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  have e1 := hc.ep
  have e2 := hc.eq
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h0.base _ _ G.V' G₁.W _ _ _ _ h0.geo.hV' h1.geo.hW
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ o' _ _ _ _ (hT F E σ B _ _ G X0 o o' h0).2.1 _ G.V' G₁.W H' _ _ M₁ rfl
    hc.hH' hM₁
  obtain ⟨C₀, C₁, -, hC₁, H0⟩ := hB F E σ B _ _ _ _ G.V' G.W G₁.V' G₁.W H H' _ _ _ _ G₁.q (b - G₁.q) (a + b - (G₁.p + G₁.q))
    (G₁.p + G₁.q) G.M' G₁.M' hc.hH hc.hH' M₁ e₀ e hM₁ h1.geo.hM' he₀ he ((a - (b + 2)) / 2 + 1) ⟨by omega, by omega⟩ K μK μ
    (hI F E σ B _ _ G.V' _ _ H h0.base h0.geo.hV' (adapted_x_ne hc.hH) hc.hH.xx K hK1) hμK hμ
  refine ⟨C₁, hC₁, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).2.1
  have hp₁ := (hT F E σ B _ _ G₁ X om₁ om₁' h₁).2.1
  obtain ⟨om₂, hp₂⟩ := hW _ _ hp.hX hp.hW hp.resX hp₁.resW M₁ hM₁
  obtain ⟨-, hf⟩ := hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ.1
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om' om₂ om₁' (IsPair.cast hp (by omega) (by omega) (by omega) (by omega))
    (IsPair.cast hp₂ (by omega) (by omega) rfl rfl) hp₁ Φ hΦ.2 hf
  have := split_uniq hU h hc.hH' hs (fa' := A₀) (fb' := A₁) ⟨c1, c2, lawα (n := 0) rfl c3 (by simp) (by push_cast; ring)⟩
  rw [this.2, (c4 g m hm x).1]
  rfl

end PositivityTheory.ThKCT

end
end

section
noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open Matrix (vecMulVec)

theorem mixAB_of (hW : MixW) (hX : MixX) (hZ : EvZero) (hP : PairEx) (hE : ThetaExp) (hU : EvUniq) : MixAB := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' χX χW om om₀ hp hp₀
  have hB := hp.base
  have hψ := hB.std
  have p := pg_herm hB hH hp.herm
  have p' := pg_skew hB hH' hp.skew
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨⟨M₁, g₁⟩, h1⟩ := hP F E σ B hB n d₁ X W₁ _ _ _ _ hp.herm hp₀.skew
    obtain ⟨om₁, hp₁⟩ := h1 χX χW hp.hX hp.hW hp.resX hp₀.resW M₁ g₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B n d X W M χX χW om _ _ _ _ hp d₁ X W₁ H' i₀ i₁ M₁ rfl hH' g₁
    obtain ⟨⟨e₁, he₁⟩, h2⟩ := hX F E σ B n d₁ X W₁ M₁ χX χW om₁ _ _ _ _ hp₁ n₁ X₁ H j₀ j₁ M₀ om₀ _ _ hH hp₀
    have hc := isEv_comp hψ hp.good g₁ hp₀.good he₀ he₁
      (comp_ne (polX p (skew_det hp₀.skew)) hE hB hp.good g₁ hp₀.good he₀ he₁) (K := isoA H H') (by
        rintro u (h | ⟨z, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨_, ⟨z, rfl⟩, by rw [incM_one, Matrix.one_mul, vv_mul_r]⟩)
    rw [Matrix.one_mul, Matrix.mul_one] at hc
    obtain ⟨c, -, hc⟩ := (polA p p').uniq hU hB hp.good hp₀.good (isEv_sumA hψ p' hc) (isEv_sumA hψ p' he)
    intro t g₁ q hq u hu t' h₁ q' hq' u' hu' Φ hΦ
    rw [hc _ (pair_pres hp _ hΦ), hc _ hΦ, LinearMap.comp_apply, LinearMap.comp_apply,
      hW F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ M₁ om₁ _ _ hH' hp₁ e₀ he₀ _ t' h₁ q' hq' u' hu' Φ hΦ, map_smul,
      h2 e₁ he₁ h₁ t g₁ q hq u hu _ (he₀.maps Φ hΦ), map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  · obtain ⟨⟨M₁, g₁⟩, h1⟩ := hP F E σ B hB n₁ d X₁ W _ _ _ _ hp₀.herm hp.skew
    obtain ⟨om₁, hp₁⟩ := h1 χX χW hp.hX hp.hW hp₀.resX hp.resW M₁ g₁
    obtain ⟨⟨e₀, he₀⟩, h2⟩ := hX F E σ B n d X W M χX χW om _ _ _ _ hp n₁ X₁ H j₀ j₁ M₁ om₁ _ _ hH hp₁
    obtain ⟨⟨e₁, he₁⟩, -⟩ := hZ F E σ B n₁ d X₁ W M₁ χX χW om₁ _ _ _ _ hp₁ d₁ X₁ W₁ H' i₀ i₁ M₀ rfl hH' hp₀.good
    have hc := isEv_comp hψ hp.good g₁ hp₀.good he₀ he₁
      (comp_ne (pol0 (herm_det hp₀.herm) p') hE hB hp.good g₁ hp₀.good he₀ he₁) (K := isoB H H') (by
        rintro u (h | ⟨z, rfl⟩)
        · exact Or.inl h
        · exact Or.inr ⟨_, ⟨z, rfl⟩, by rw [incM_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec]⟩)
    rw [Matrix.one_mul, Matrix.mul_one] at hc
    obtain ⟨c, -, hc⟩ := (polB p p').uniq hU hB hp.good hp₀.good (isEv_sumB hψ p hc) (isEv_sumB hψ p he)
    intro t g₁ q hq u hu t' h₁ q' hq' u' hu' Φ hΦ
    rw [hc _ (pair_pres hp _ hΦ), hc _ hΦ, LinearMap.comp_apply, LinearMap.comp_apply,
      h2 e₀ he₀ _ t g₁ q hq u hu Φ hΦ, map_smul,
      hW F E σ B n₁ d X₁ W M₁ χX χW om₁ _ _ _ _ hp₁ d₁ W₁ H' i₀ i₁ M₀ om₀ _ _ hH' hp₀ e₁ he₁ _ t' h₁ q' hq' u' hu' _ (he₀.maps Φ hΦ),
      map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring

end PositivityTheory.ThKCT.Ker
end
end

section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open Matrix (vecMulVec)

theorem split_triv {A I J : Type} {e : I → A → ℂ} {c : I → ℂ} {j : J → I} (hj : Function.Injective j) (h1 : ∀ k a, e (j k) a = 1)
    {a : A} {S : ℂ} (h : HasSum (fun i => c i * e i a) S) :
    HasSum (fun i : ↥(Set.range j)ᶜ => c i * e i a) (S - ∑' k, c (j k)) := by
  have h2 := h.summable.tsum_subtype_add_tsum_subtype_compl (Set.range j)
  rw [tsum_range (fun i => c i * e i a) hj, h.tsum_eq] at h2
  simp only [h1, mul_one] at h2
  rw [← h2, add_sub_cancel_left]
  exact (h.summable.subtype _).hasSum

theorem triv_part {A I₁ I₂ J₁ J₂ : Type} [AddCommGroup A] {e₁ : I₁ → A → ℂ} {e₂ : I₂ → A → ℂ} {c₁ : I₁ → ℂ} {c₂ : I₂ → ℂ}
    {j₁ : J₁ → I₁} {j₂ : J₂ → I₂} (i₁ : Function.Injective j₁) (i₂ : Function.Injective j₂)
    (m₁ : ∀ i a b, e₁ i (a + b) = e₁ i a * e₁ i b) (m₂ : ∀ i a b, e₂ i (a + b) = e₂ i a * e₂ i b)
    (l₁ : ∀ i a, ‖e₁ i a‖ ≤ 1) (l₂ : ∀ i a, ‖e₂ i a‖ ≤ 1) (t₁ : ∀ k a, e₁ (j₁ k) a = 1) (t₂ : ∀ k a, e₂ (j₂ k) a = 1)
    (n₁ : ∀ i ∉ Set.range j₁, ∃ a, e₁ i a ≠ 1) (n₂ : ∀ i ∉ Set.range j₂, ∃ a, e₂ i a ≠ 1) (s₁ : Summable c₁) (s₂ : Summable c₂)
    {S : A → ℂ} (h₁ : ∀ a, HasSum (fun i => c₁ i * e₁ i a) (S a)) (h₂ : ∀ a, HasSum (fun i => c₂ i * e₂ i a) (S a)) :
    ∑' k, c₁ (j₁ k) = ∑' k, c₂ (j₂ k) := by
  refine sub_eq_zero.1 (GlobalTheory.CompanionTheory.ThetaInj.charSeries_coeff_eq_zero (A := A) (I := Unit ⊕ (↥(Set.range j₁)ᶜ ⊕ ↥(Set.range j₂)ᶜ))
    (Sum.elim (fun _ _ => 1) (Sum.elim (fun i => e₁ i) fun i => e₂ i))
    (Sum.elim (fun _ => ∑' k, c₁ (j₁ k) - ∑' k, c₂ (j₂ k)) (Sum.elim (fun i => c₁ i) fun i => -c₂ i)) (Sum.inl ())
    ?_ ?_ (fun _ => rfl) ?_ (Summable.norm ?_) fun a => ?_)
  · rintro (_ | i | i) a b
    exacts [(one_mul _).symm, m₁ i a b, m₂ i a b]
  · rintro (_ | i | i) a
    exacts [norm_one.le, l₁ i a, l₂ i a]
  · rintro (_ | i | i) h
    exacts [absurd rfl h, n₁ i i.2, n₂ i i.2]
  · exact Summable.sum _ Summable.of_finite (Summable.sum _ (s₁.subtype _) (s₂.subtype _).neg)
  · refine HasSum.tsum_eq ?_
    have k₂ : HasSum (fun i : ↥(Set.range j₂)ᶜ => -c₂ i * e₂ i a) (-(S a - ∑' k, c₂ (j₂ k))) := by
      simpa only [neg_mul] using (split_triv i₂ t₂ (h₂ a)).neg
    rw [show (0 : ℂ) = (∑' k, c₁ (j₁ k) - ∑' k, c₂ (j₂ k)) * 1 + ((S a - ∑' k, c₁ (j₁ k)) + -(S a - ∑' k, c₂ (j₂ k))) by ring]
    refine HasSum.sum (hasSum_unique _) (HasSum.sum ?_ ?_)
    · exact split_triv i₁ t₁ (h₁ a)
    · exact k₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {H : Plane E n n₁} {H' : Plane E d d₁} {ε ε' : ℤ}

theorem PG.eps_ne (h : PG σ X X₁ H ε) : (ε : E) ≠ 0 := left_ne_zero_of_mul_eq_one h.rat.ee

theorem PG.nd_low' (h : PG σ X X₁ H ε) (u) (hu : ∀ z, bf σ.toRingHom X.J (H.ι *ᵥ u) (H.ι *ᵥ z) = 0) : u = 0 :=
  h.nd_low u fun z => by rw [h.rat.symm, hu, map_zero, mul_zero]

theorem PG.line (h : PG σ X X₁ H ε) (a) (h1 : bf σ.toRingHom X.J a H.x = 0) (h2 : ∀ z, bf σ.toRingHom X.J a (H.ι *ᵥ z) = 0) :
    ∃ ξ : E, ξ • H.x = a := by
  obtain ⟨s, t, z, rfl⟩ := h.rat.span a
  simp only [bf_add_l, bf_smul_l, h.rat.xx, h.rat.ix, h.rat.yx, h.rat.xi, h.rat.yi, mul_zero, zero_add, add_zero] at h1 h2
  refine ⟨s, ?_⟩
  rw [h.nd_low' z h2, (mul_eq_zero.1 h1).resolve_right h.eps_ne]
  simp

theorem PG.x_ne (h : PG σ X X₁ H ε) : H.x ≠ 0 := fun h0 => by
  have := h.rat.xy
  rw [h0] at this
  simp [bf] at this

variable (H H') in

def capAB : Submodule (AE F E) (Ten F E n d) where
  carrier := sumA H H' ∩ sumB H H'
  zero_mem' := ⟨⟨0, 0, by simp [vv0]⟩, ⟨0, 0, by simp [vv0]⟩⟩
  add_mem' := by
    rintro a b ⟨⟨y, z, e⟩, ⟨z', y', e'⟩⟩ ⟨⟨y₁, z₁, e₁⟩, ⟨z₁', y₁', e₁'⟩⟩
    refine ⟨⟨y + y₁, z + z₁, ?_⟩, ⟨z' + z₁', y' + y₁', ?_⟩⟩
    · rw [e, e₁, Matrix.add_vecMulVec, Matrix.mulVec_add, Matrix.vecMulVec_add]; abel
    · rw [e', e₁', Matrix.mulVec_add, Matrix.add_vecMulVec, Matrix.vecMulVec_add]; abel
  smul_mem' := by
    rintro c a ⟨⟨y, z, e⟩, ⟨z', y', e'⟩⟩
    refine ⟨⟨c • y, c • z, ?_⟩, ⟨c • z', c • y', ?_⟩⟩
    · rw [e, Matrix.smul_vecMulVec, Matrix.mulVec_smul, Matrix.vecMulVec_smul, smul_add]
    · rw [e', Matrix.mulVec_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_add]

theorem cap_xx : incM F (vecMulVec H.x H'.x) ∈ capAB (F := F) H H' := by
  rw [incM_vv]
  exact ⟨⟨incV F H.x, 0, by simp [vv0]⟩, ⟨incV F H'.x, 0, by simp [vv0]⟩⟩

theorem cap_ix (u) : incM F (vecMulVec (H.ι *ᵥ u) H'.x) ∈ capAB (F := F) H H' := by
  rw [incM_vv, ← inc_mulVec]
  exact ⟨⟨incM F H.ι *ᵥ incV F u, 0, by simp [vv0]⟩, ⟨0, incV F u, by simp [vv0]⟩⟩

theorem cap_xi (u) : incM F (vecMulVec H.x (H'.ι *ᵥ u)) ∈ capAB (F := F) H H' := by
  rw [incM_vv, ← inc_mulVec]
  exact ⟨⟨0, incV F u, by simp [vv0]⟩, ⟨incM F H'.ι *ᵥ incV F u, 0, by simp [vv0]⟩⟩

theorem incM_smul (l : E) (v : Matrix (Fin n) (Fin d) E) : incM F (l • v) = inclR (F := F) (AF F) l • incM F v := by
  ext i j
  simp [incM]

theorem exists_ne (M : Model σ X W) (hψ : IsStd B.ψ) (cc : ∀ a, σ (σ a) = a) {x v : Matrix (Fin n) (Fin d) E}
    (hv : incM F v ∈ capAB (F := F) H H') (h : hTens σ X.J W.J x v ≠ 0) :
    ∃ a : capAB (F := F) H H', B.ψ (sy σ X W (incM F x) a.1) ≠ 1 := by
  obtain ⟨l, hl⟩ : ∃ l, Algebra.trace F E (-hTens σ X.J W.J x v * l) ≠ 0 := by
    by_contra h0
    push Not at h0
    exact h (neg_eq_zero.1 ((traceForm_nondegenerate F E).1 _ fun a => h0 a))
  obtain ⟨b, hb⟩ := DFunLike.ne_iff.1 (std_ne_one hψ)
  refine ⟨⟨(b * algebraMap F (AF F) (Algebra.trace F E (-hTens σ X.J W.J x v * l))⁻¹) • incM F (σ l • v), ?_⟩, ?_⟩
  · rw [← algebraMap_smul (AE F E), incM_smul]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hv)
  · have e := sy_inc (σ := σ) (X := X) (W := W) x (σ l • v)
    rw [hT_smul_r, cc, mul_comm, ← neg_mul] at e
    change B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _) ≠ 1
    rw [form_eq M.co, map_smul, ← form_eq M.co, show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) _ _ = _ from e,
      smul_eq_mul, mul_assoc, ← map_mul, inv_mul_cancel₀ hl, map_one, mul_one]
    simpa using hb

theorem twoExp_of (hE : ThetaExp) : TwoExp := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' hB hX hW hM hM₀ eA eB hA hBv
  have hψ := hB.std
  have p := pg_herm hB hH hX
  have p' := pg_skew hB hH' hW
  have hA' := isEv_sumA hψ p' hA
  have hB' := isEv_sumB hψ p hBv
  obtain ⟨C, hC, h1⟩ := (polA p p').exp hE hB hM hM₀ hA'
  obtain ⟨C', hC', h2⟩ := (polB p p').exp hE hB hM hM₀ hB'
  have eA' : ∀ ξ : E, vA H.y H'.y H'.ι (ξ • H.x, 0) = ξ • vecMulVec H.x H'.y := fun ξ => by
    simp [vv0, vA_apply, Matrix.smul_vecMulVec]
  have eB' : ∀ ξ : E, vB H.y H'.y H.ι (ξ • H'.x, 0) = ξ • vecMulVec H.y H'.x := fun ξ => by
    simp [vB_apply, Matrix.vecMulVec_smul]
  have iA : Function.Injective fun ξ : E => ((ξ • H.x, 0) : (Fin n → E) × (Fin d₁ → E)) := fun a b e =>
    smul_left_injective E p.x_ne (congrArg Prod.fst e)
  have iB : Function.Injective fun ξ : E => ((ξ • H'.x, 0) : (Fin d → E) × (Fin n₁ → E)) := fun a b e =>
    smul_left_injective E p'.x_ne (congrArg Prod.fst e)
  have hm : ∀ x a b, B.ψ (sy σ X W x (a + b)) = B.ψ (sy σ X W x a) * B.ψ (sy σ X W x b) := fun x a b => by
    rw [← AddChar.map_add_eq_mul]
    exact congrArg B.ψ ((formL M.co x).map_add a b)
  refine ⟨C⁻¹ * C', mul_ne_zero (inv_ne_zero hC) hC', fun Ψ hΨ => ⟨?_, ?_, ?_⟩⟩
  · simpa only [Function.comp_def, eA'] using ((summable_mul_left_iff hC).1 (h1 Ψ hΨ).summable).comp_injective iA
  · simpa only [Function.comp_def, eB'] using ((summable_mul_left_iff hC').1 (h2 Ψ hΨ).summable).comp_injective iB
  have key := triv_part (A := capAB (F := F) H H') (e₁ := fun t a => B.ψ (sy σ X W (incM F (vA H.y H'.y H'.ι t)) a.1))
    (e₂ := fun t a => B.ψ (sy σ X W (incM F (vB H.y H'.y H.ι t)) a.1)) iA iB (fun t a b => hm _ _ _) (fun t a b => hm _ _ _)
    (fun _ _ => (std_norm hψ _).le) (fun _ _ => (std_norm hψ _).le) ?_ ?_ ?_ ?_ (h1 Ψ hΨ).summable (h2 Ψ hΨ).summable
    (S := fun a => thetaSum F (M.co.rho B.ψ a.1 Ψ)) (fun a => ?_) (fun a => ?_)
  · simp only [eA', eB', tsum_mul_left] at key
    rw [mul_assoc, ← key, inv_mul_cancel_left₀ hC]
  · rintro ξ ⟨_, -, y, z, rfl⟩
    rw [eA', sy_of_hT, AddChar.map_zero_eq_one]
    rw [incM_smul, incM_vv, hT_smul_l, hT_add_r, hT_vv, hT_vv, p.ad.xx, p.ad.xi]
    simp
  · rintro ξ ⟨_, ⟨y, z, rfl⟩, -⟩
    rw [eB', sy_of_hT, AddChar.map_zero_eq_one]
    rw [incM_smul, incM_vv, hT_smul_l, hT_add_r, hT_vv, hT_vv, p'.ad.xx, p'.ad.xi]
    simp
  · rintro ⟨a, b⟩ hn
    by_contra h0
    have k : ∀ v, incM F v ∈ capAB (F := F) H H' → hTens σ X.J W.J (vA H.y H'.y H'.ι (a, b)) v = 0 := fun v hv => by
      by_contra h3
      exact h0 (exists_ne M hψ p.rat.cc hv h3)
    have k1 := k _ cap_xx
    have k2 := fun u => k _ (cap_ix u)
    have k3 := fun u => k _ (cap_xi u)
    simp only [vA_apply, hT_add_l, hT_vv, p'.rat.yx, p'.rat.ix, p'.rat.yi, p.rat.yx, p.rat.yi, mul_zero, add_zero, zero_add,
      mul_eq_zero, p.eps_ne, p'.eps_ne, or_false, false_or] at k1 k2 k3
    obtain ⟨ξ, rfl⟩ := p.line a k1 k2
    exact hn ⟨ξ, by rw [p'.nd_low' b k3]⟩
  · rintro ⟨a, b⟩ hn
    by_contra h0
    have k : ∀ v, incM F v ∈ capAB (F := F) H H' → hTens σ X.J W.J (vB H.y H'.y H.ι (a, b)) v = 0 := fun v hv => by
      by_contra h3
      exact h0 (exists_ne M hψ p.rat.cc hv h3)
    have k1 := k _ cap_xx
    have k2 := fun u => k _ (cap_xi u)
    have k3 := fun u => k _ (cap_ix u)
    simp only [vB_apply, hT_add_l, hT_vv, p'.rat.yx, p.rat.ix, p'.rat.yi, p.rat.yx, p.rat.yi, zero_mul, add_zero, zero_add,
      mul_eq_zero, p.eps_ne, p'.eps_ne, or_false, false_or] at k1 k2 k3
    obtain ⟨ξ, rfl⟩ := p'.line a k1 k2
    exact hn ⟨ξ, by rw [p.nd_low' b k3]⟩
  · convert h1 _ (rho_mem M hψ a.1 hΨ) using 2 with t
    rw [rho_comm, map_smul, hA'.inv _ a.2.1 _ (rho_mem M hψ _ hΨ), thetaSum_smul]
    ring
  · convert h2 _ (rho_mem M hψ a.1 hΨ) using 2 with t
    rw [rho_comm, map_smul, hB'.inv _ a.2.2 _ (rho_mem M hψ _ hΨ), thetaSum_smul]
    ring

end PositivityTheory.ThKCT.Ker
end
end

section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField.mixedEmbedding
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.HeisSchA PositivityTheory.ThKCT.Arch PositivityTheory.ThKCT.Ad

namespace Ad

variable {F : Type} [Field F] [NumberField F] {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]

theorem norm_le_sum (x : mixedSpace F) : ‖x‖ ≤ ∑ w : InfinitePlace F, normAtPlace w x := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.sup'_le _ _ fun w hw => Finset.single_le_sum (fun v _ => normAtPlace_nonneg v x) hw

theorem sum_le_norm (x : mixedSpace F) : ∑ w : InfinitePlace F, normAtPlace w x ≤ Fintype.card (InfinitePlace F) * ‖x‖ := by
  rw [← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun w hw => ?_
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => normAtPlace w x) hw

set_option maxHeartbeats 800000 in
theorem slice_core {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ)
    (ei : SInf F κ →L[ℂ] SInf F κ₁) (ef : ((κ → Af F) → ℂ) → (κ₁ → Af F) → ℂ) (h0 : ei ≠ 0)
    (he : ∀ φ ∈ SB (κ → Af F), ef φ ∈ SB _ ∧ ∀ f : SInf F κ, e (pureA F f φ) = pureA F (ei f) (ef φ))
    {m : ℕ} (c ζ : Fin m → (κ → AF F) × (κ → AF F)) (hinv : ∀ j (a : AF F), ∀ Φ ∈ schA F κ, e (schr ψ (a • ζ j) Φ) = e Φ)
    (hp : ∀ i j, (ζ i).1 ⬝ᵥ (c j).2 - (c j).1 ⬝ᵥ (ζ i).2 = if i = j then 1 else 0) {φ : (κ → Af F) → ℂ} (hφ : φ ∈ SB _) :
    ∃ (r : ℕ) (φ₁ : Fin r → (κ₁ → Af F) → ℂ) (C : Set (Fin m → Af F))
      (A : Fin r → (Fin m → AF F) → SInf F κ →L[ℂ] SInf F κ₁),
      (∀ i, φ₁ i ∈ SB _) ∧ IsCompact C ∧ (∀ i f, Continuous fun y => A i y f) ∧
      (∀ y (f : SInf F κ), e (schr ψ (∑ j, y j • c j) (pureA F f φ)) = ∑ i, pureA F (A i y f) (φ₁ i)) ∧
      (∀ i y, (fun j => (y j).2) ∉ C → A i y = 0) ∧
      ∀ (q : Seminorm ℂ (SInf F κ₁)) (N : ℕ), Continuous q → ∃ p : Seminorm ℂ (SInf F κ),
        Continuous p ∧ ∀ i y f, q (A i y f) * (1 + ∑ j, ∑ w : InfinitePlace F, normAtPlace w (evI F (y j))) ^ N ≤ p f := by
  have key : ∀ (y : Fin m → AF F) j (a : AF F), ∀ Φ ∈ schA F κ,
      e (schr ψ (∑ i, y i • c i) (schr ψ (a • ζ j) Φ)) = ψ (-(a * y j)) • e (schr ψ (∑ i, y i • c i) Φ) := fun y j a Φ hΦ => by
    rw [schr_comm, map_smul, hinv _ _ _ (schr_mem_schA ψ hψ _ _ hΦ)]
    congr 2
    have : a * y j = ∑ i, a * y i * ((ζ j).1 ⬝ᵥ (c i).2 - (c i).1 ⬝ᵥ (ζ j).2) := by simp [hp]
    rw [this]
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, sum_dotProduct, dotProduct_sum, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  let wy : (Fin m → AF F) → _ := fun y => aw0 F κ (∑ j, qI F (y j) • ev2 (c j))
  let T : (Fin m → AF F) → SInf F κ →L[ℂ] SInf F κ₁ := fun y => ei.comp (S (wy y))
  let G : (Fin m → Af F) → (κ₁ → Af F) → ℂ := fun b => ef (fw ψ (∑ j, b j • fn2 (c j)) φ)
  have main : ∀ y (f : SInf F κ), e (schr ψ (∑ j, y j • c j) (pureA F f φ)) = pureA F (T y f) (G fun j => p2 (y j)) :=
    fun y f => by rw [schr_pure hψ, (he _ (fw_mem hψ _ hφ)).2, pairEvaluation_linear_combination, pairFunctional_linear_combination]; rfl
  have hG : IsLocallyConstant G := ((fw_lc hψ hφ).comp_continuous (f := fun b : Fin m → Af F => ∑ j, b j • fn2 (c j))
    (continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const)).comp ef
  have hGm : ∀ b, G b ∈ SB _ := fun b => (he _ (fw_mem hψ _ hφ)).1
  obtain ⟨C, hC, hC'⟩ : ∃ C : Set (Fin m → Af F), IsCompact C ∧ ∀ b, G b ≠ 0 → b ∈ C := by
    have hU : ∀ᶠ a : Af F in 𝓝 0, ∀ j, fw ψ (a • fn2 (ζ j)) φ = φ := eventually_all.2 fun j => by
      have := ((fw_lc hψ hφ).comp_continuous (f := fun a : Af F => a • fn2 (ζ j))
        (continuous_id.smul continuous_const)).eventually_eq 0
      simpa only [Function.comp_apply, zero_smul, fw_zero] using this
    obtain ⟨C₀, h₀, h₀'⟩ := annih hψ hU
    refine ⟨Set.pi Set.univ fun _ => -C₀, isCompact_univ_pi fun _ => h₀.neg, fun b hb j _ => h₀' _ fun a ha => ?_⟩
    obtain ⟨f₀, hf₀⟩ : ∃ f₀, ei f₀ ≠ 0 := by
      by_contra! h
      exact h0 (ContinuousLinearMap.ext h)
    let y : Fin m → AF F := fun j => pt 0 (b j)
    have h1 := key y j (pt 0 a) _ (pureA_mem (S (-wy y) f₀) hφ)
    rw [schr_pure hψ (pt 0 a • ζ j), pairEvaluation_smul, pairFunctional_smul, qI_pt, finite_projection_mixed_point, ha j, zero_smul, map_zero, S_zero, main,
      ← pureA_smul_left] at h1
    have h2 := pureA_cancel hb h1
    rw [show T y (S (-wy y) f₀) = ei f₀ from congrArg ei (S_neg _ _)] at h2
    have h3 : ψ (-(pt 0 a * y j)) = 1 := by
      by_contra h
      exact hf₀ ((smul_eq_zero.1 (show (ψ (-(pt 0 a * y j)) - 1) • ei f₀ = 0 by
        rw [sub_smul, one_smul, ← h2, sub_self])).resolve_left (sub_ne_zero.2 h))
    rw [psi_eq hψ, map_neg, map_mul, qI_pt, zero_mul, neg_zero, map_zero, map_neg, map_mul, finite_projection_mixed_point, finite_projection_mixed_point] at h3
    simpa using h3
  have hfin : (G '' C \ {0}).Finite := by
    haveI := isCompact_iff_compactSpace.1 hC
    have := (hG.comp_continuous (continuous_subtype_val : Continuous ((↑) : C → _))).range_finite
    rw [Set.range_comp, Subtype.range_coe] at this
    exact this.diff
  let φ₁ : Fin hfin.toFinset.card → (κ₁ → Af F) → ℂ := fun i => (hfin.toFinset.equivFin.symm i).1
  have hφ₁ : ∀ i, φ₁ i ∈ G '' C \ {0} := fun i => hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm i).2
  let A : Fin hfin.toFinset.card → (Fin m → AF F) → SInf F κ →L[ℂ] SInf F κ₁ := fun i y =>
    if G (fun j => p2 (y j)) = φ₁ i then T y else 0
  have z0 : ∀ g : (κ₁ → Af F) → ℂ, pureA F (0 : SInf F κ₁) g = 0 := fun g => funext fun x => zero_mul _
  obtain ⟨K₁, hK₁, hK₁'⟩ := (LinearMap.toContinuousLinearMap (aw0 F κ)).bound
  refine ⟨_, φ₁, C, A, fun i => by obtain ⟨b, -, hb⟩ := (hφ₁ i).1; exact hb ▸ hGm b, hC, fun i f => ?_, fun y f => ?_,
    fun i y hy => if_neg fun h : G (fun j => p2 (y j)) = φ₁ i => hy (hC' _ fun h' => (hφ₁ i).2 (h.symm.trans h')), fun q N hq => ?_⟩
  · have h1 : IsLocallyConstant fun y : Fin m → AF F => if G (fun j => p2 (y j)) = φ₁ i then (1 : ℂ) else 0 :=
      (hG.comp_continuous (f := fun (y : Fin m → AF F) j => p2 (y j))
        (continuous_pi fun j => continuous_snd.comp (continuous_apply j))).comp fun g => if g = φ₁ i then (1 : ℂ) else 0
    have h2 : Continuous wy := (aw0 F κ).continuous_of_finiteDimensional.comp
      (continuous_finsetSum _ fun j _ => Continuous.smul (f := fun y : Fin m → AF F => qI F (y j))
        (continuous_qI.comp (continuous_apply j)) continuous_const)
    refine (h1.continuous.smul (ei.continuous.comp ((continuous_S f).comp h2))).congr fun y => ?_
    simp only [A]
    split_ifs with h
    · simp [h, T]
    · simp [h]
  · rw [main]
    by_cases h : G (fun j => p2 (y j)) = 0
    · rw [h, GlobalTheory.ThK.Dbl.Dense.pureA_zero]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      simp only [A]
      rw [if_neg fun h' => (hφ₁ i).2 (h'.symm.trans h)]
      exact z0 _
    · let i₀ := hfin.toFinset.equivFin ⟨G fun j => p2 (y j), hfin.mem_toFinset.2 ⟨⟨_, hC' _ h, rfl⟩, h⟩⟩
      have hi : G (fun j => p2 (y j)) = φ₁ i₀ := by simp only [φ₁, i₀, Equiv.symm_apply_apply]
      rw [Finset.sum_eq_single i₀ (fun i _ hne => ?_) fun h => absurd (Finset.mem_univ _) h]
      · simp only [A]
        rw [if_pos hi, ← hi]
      · simp only [A]
        rw [if_neg fun h' => hne (hfin.toFinset.equivFin.symm.injective (Subtype.ext (h'.symm.trans hi)))]
        exact z0 _
  · obtain ⟨p, M, hp, hp'⟩ := grow (q.comp ei.toLinearMap) (hq.comp ei.continuous)
    obtain ⟨K, hK, hK'⟩ := exists_half_trace (F := F)
    let s : (Fin m → AF F) → ℝ := fun y => ∑ j, ∑ w : InfinitePlace F, normAtPlace w (qI F (y j))
    have hs0 : ∀ (y : Fin m → AF F) j, 0 ≤ ∑ w : InfinitePlace F, normAtPlace w (qI F (y j)) := fun y j =>
      Finset.sum_nonneg fun w _ => normAtPlace_nonneg _ _
    have hs : ∀ y, 0 ≤ s y := fun y => Finset.sum_nonneg fun j _ => hs0 y j
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∑ j, ‖ev2 (ζ j)‖ := ⟨_, rfl⟩
    obtain ⟨Cc, hCc⟩ : ∃ Z, Z = ∑ j, ‖ev2 (c j)‖ := ⟨_, rfl⟩
    have hCc0 : 0 ≤ Cc := hCc ▸ Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hZ0 : 0 ≤ Z := hZ ▸ Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hZ1 : ∀ j, ‖ev2 (ζ j)‖ ≤ Z := fun j =>
      hZ ▸ Finset.single_le_sum (f := fun j => ‖ev2 (ζ j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    have hKC : 0 ≤ (1 + K₁ * Cc) ^ M := pow_nonneg (add_nonneg zero_le_one (mul_nonneg hK₁.le hCc0)) _
    refine (decay (Y := Fin hfin.toFinset.card × (Fin m → AF F)) (fun x => (A x.1 x.2).toLinearMap)
      (fun x => s x.2) (fun x => hs x.2) (K₁ * Z * (m * Fintype.card (InfinitePlace F)) * K) (fun x hy => ?_) q
      (sc ((1 + K₁ * Cc) ^ M) p) (sc_cont _ hp) M (fun x f => ?_) N).imp fun p' h => ⟨h.1, fun i y f => h.2 (i, y) f⟩
    · obtain ⟨i, y⟩ := x
      change 0 < s y at hy
      have hm : (Finset.univ : Finset (Fin m)).Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        simp only [s, h, Finset.sum_empty, lt_irrefl] at hy
      obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖qI F (y j)‖) hm
      have h1 : s y ≤ m * Fintype.card (InfinitePlace F) * ‖qI F (y j)‖ := by
        refine (Finset.sum_le_card_nsmul _ _ (Fintype.card (InfinitePlace F) * ‖qI F (y j)‖) fun i hi =>
          (sum_le_norm _).trans (mul_le_mul_of_nonneg_left (hj i hi) (Nat.cast_nonneg _))).trans (le_of_eq ?_)
        rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      obtain ⟨α, hα, hα'⟩ := hK' (qI F (y j)) fun h => by
        rw [h, norm_zero, mul_zero] at h1
        exact absurd hy (not_lt.2 h1)
      refine ⟨aw0 F κ (α • ev2 (ζ j)), ?_, fun f => ?_⟩
      · have h2 : ‖aw0 F κ (α • ev2 (ζ j))‖ ≤ K₁ * (‖α‖ * Z) := (hK₁' _).trans (mul_le_mul_of_nonneg_left
          ((norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hZ1 j) (norm_nonneg _))) hK₁.le)
        calc _ ≤ K₁ * (‖α‖ * Z) * (m * Fintype.card (InfinitePlace F) * ‖qI F (y j)‖) :=
              mul_le_mul h2 h1 (hs y) (mul_nonneg hK₁.le (mul_nonneg (norm_nonneg _) hZ0))
          _ = K₁ * Z * (m * Fintype.card (InfinitePlace F)) * (‖α‖ * ‖qI F (y j)‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hα
            (mul_nonneg (mul_nonneg hK₁.le hZ0) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      · simp only [A]
        split_ifs with h
        · have h1 := key y j (pt α 0) _ (pureA_mem f hφ)
          rw [schr_pure hψ (pt α 0 • ζ j), pairEvaluation_smul, pairFunctional_smul, qI_pt, finite_projection_mixed_point, zero_smul, fw_zero, main, main,
            ← pureA_smul_left] at h1
          have h2 := pureA_cancel (h ▸ (hφ₁ i).2) h1
          have h3 : ψ (-(pt α 0 * y j)) = -1 := by
            rw [psi_eq hψ, map_neg, map_mul, qI_pt, map_neg, mul_comm α, hα', map_neg, map_mul, finite_projection_mixed_point, zero_mul, neg_zero,
              AddChar.map_zero_eq_one, mul_one, ← Complex.exp_pi_mul_I]
            congr 1
            push_cast
            ring
          rw [h3, neg_one_smul] at h2
          exact h2
        · simp
    · obtain ⟨i, y⟩ := x
      rw [sc_apply hKC]
      have h1 : ‖wy y‖ ≤ K₁ * (s y * Cc) := (hK₁' _).trans (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (by
        rw [hCc, Finset.mul_sum]
        refine Finset.sum_le_sum fun j hj => (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        exact (norm_le_sum _).trans (Finset.single_le_sum (fun j _ => hs0 y j) hj))) hK₁.le)
      have h2 := hs y
      have h3 := apply_nonneg p f
      simp only [A]
      split_ifs with h
      · refine (hp' (wy y) f).trans ?_
        rw [← mul_assoc, ← mul_pow]
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg _)) ?_ _) h3
        have h4 := mul_nonneg hK₁.le hCc0
        change 1 + ‖wy y‖ ≤ (1 + s y) * (1 + K₁ * Cc)
        generalize ‖wy y‖ = a, s y = b at h1 h2 ⊢
        nlinarith
      · simp only [ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_apply, map_zero]
        exact mul_nonneg (pow_nonneg (add_nonneg zero_le_one h2) _) (mul_nonneg hKC h3)

end Ad

theorem slice_of : Slice := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hD φ hφ
  obtain ⟨ei, ef, h0, h⟩ := ev_pure hM hM₁ he
  obtain ⟨r, φ₁, C, A, h1, h2, h3, h4, h5⟩ := slice_core hB.std e ei ef h0 h (fun j => M.co.e (incM F (u j)))
    (fun j => M.co.e (incM F (z j))) (fun j a Φ hΦ => by rw [← map_smul]; exact he.inv _ (hD.mem j a) Φ hΦ)
    (fun i j => by rw [← M.co.form]; convert hD.pair i j) hφ
  refine ⟨r, φ₁, C, A, h1, h2, h3, fun y f => ?_, h5⟩
  rw [← h4, Darboux.rho, lin, map_sum]
  simp only [map_smul]

theorem evAdm_of : EvAdm := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁
  refine ⟨exists_adm_eq_thetaSum_of_locallyCompact F _, fun u Φ hΦ => schr_mem_schA _ hB.std _ Φ hΦ, fun ι ι' I e he u l hl => ?_⟩
  obtain ⟨ei, ef, -, h⟩ := ev_pure hM hM₁ he
  let R : Fn F n d →ₗ[ℂ] Fn F n d :=
    { toFun := M.co.rho B.ψ u
      map_add' := fun φ φ' => funext fun x => by simp only [Darboux.rho, schr, Pi.add_apply]; ring
      map_smul' := fun a φ => funext fun x => by
        simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  refine ⟨l ∘ₗ e ∘ₗ R, fun g hg => ?_, fun Φ _ => rfl⟩
  obtain ⟨h1, h2⟩ := h _ (fw_mem hB.std (fn2 (M.co.e u)) hg)
  obtain ⟨T, hT⟩ := hl _ h1
  refine ⟨T.comp (ei.comp (S (aw0 F _ (ev2 (M.co.e u))))), fun f => ?_⟩
  change l (e (schr B.ψ (M.co.e u) (pureA F f g))) = _
  rw [schr_pure hB.std, h2, hT]
  rfl

end PositivityTheory.ThKCT

end
end

section
noncomputable section

namespace PositivityTheory.ThKCT

namespace SchI

open scoped ContDiff NNReal BoundedContinuousFunction
open MeasureTheory Filter Topology

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem cd (f : SchwartzMap V ℂ) (j : ℕ) : ContDiff ℝ j f := f.smooth j

def jet (k j : ℕ) (f : SchwartzMap V ℂ) : V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ‖x‖ ^ k • iteratedFDeriv ℝ j f x)
    ((continuous_norm.pow k).smul ((cd f j).continuous_iteratedFDeriv le_rfl)) (SchwartzMap.seminorm ℂ k j f) fun x => by
      rw [norm_smul, norm_pow, norm_norm]
      exact SchwartzMap.le_seminorm ℂ k j f x

theorem jet_apply (k j : ℕ) (f : SchwartzMap V ℂ) (x : V) : jet k j f x = ‖x‖ ^ k • iteratedFDeriv ℝ j f x := rfl

theorem norm_jet (k j : ℕ) (f : SchwartzMap V ℂ) : ‖jet k j f‖ = SchwartzMap.seminorm ℂ k j f := by
  refine le_antisymm (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg _ _) _) ?_
  refine SchwartzMap.seminorm_le_bound ℂ k j f (norm_nonneg _) fun x => ?_
  have := (jet k j f).norm_coe_le_norm x
  rwa [jet_apply, norm_smul, norm_pow, norm_norm] at this

def J (k j : ℕ) : SchwartzMap V ℂ →L[ℂ] V →ᵇ (V [×j]→L[ℝ] ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (jet k j)
    (fun f g => by
      ext1 x
      rw [BoundedContinuousFunction.add_apply, jet_apply, jet_apply, jet_apply, ← smul_add]
      exact congrArg _ (iteratedFDeriv_add_apply (cd f j).contDiffAt (cd g j).contDiffAt))
    (fun a f => by
      ext1 x
      rw [BoundedContinuousFunction.smul_apply, jet_apply, jet_apply, RingHom.id_apply, smul_comm a]
      exact congrArg _ (iteratedFDeriv_const_smul_apply (cd f j).contDiffAt))
    ⟨{(k, j)}, 1, zero_le_one, fun f => by rw [norm_jet, Finset.sup_singleton, one_mul]; rfl⟩

variable {α : Type} [TopologicalSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
  {G : α → SchwartzMap V ℂ} (hG : Continuous G) (hI : ∀ k j : ℕ, Integrable (fun a => SchwartzMap.seminorm ℂ k j (G a)) μ)

include hG hI

theorem int_J (k j : ℕ) : Integrable (fun a => J k j (G a)) μ :=
  (hI k j).mono' ((J k j).continuous.comp hG).aestronglyMeasurable (.of_forall fun a => (norm_jet k j _).le)

omit hI in
theorem cont_D (j : ℕ) (x : V) : Continuous fun a => iteratedFDeriv ℝ j (G a) x := by
  have := (BoundedContinuousFunction.evalCLM ℂ x).continuous.comp ((J 0 j).continuous.comp hG)
  refine this.congr fun a => ?_
  change jet 0 j (G a) x = _
  rw [jet_apply, pow_zero, one_smul]

omit hG hI in
theorem bd_D (f : SchwartzMap V ℂ) (j : ℕ) (x : V) : ‖iteratedFDeriv ℝ j f x‖ ≤ SchwartzMap.seminorm ℂ 0 j f := by
  simpa using SchwartzMap.le_seminorm ℂ 0 j f x

theorem int_D (j : ℕ) (x : V) : Integrable (fun a => iteratedFDeriv ℝ j (G a) x) μ :=
  (hI 0 j).mono' (cont_D hG j x).aestronglyMeasurable (.of_forall fun a => bd_D _ j x)

theorem deriv_D (j : ℕ) (x : V) : HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ j (G a) y ∂μ)
    (∫ a, iteratedFDeriv ℝ (j + 1) (G a) x ∂μ).curryLeft x := by
  let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => V) ℂ
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (s := Set.univ) (x₀ := x)
    (F := fun y a => iteratedFDeriv ℝ j (G a) y) (F' := fun y a => L (iteratedFDeriv ℝ (j + 1) (G a) y))
    (bound := fun a => SchwartzMap.seminorm ℂ 0 (j + 1) (G a)) univ_mem
    (.of_forall fun y => (cont_D hG j y).aestronglyMeasurable) (int_D hG hI j x)
    (L.continuous.comp (cont_D hG (j + 1) x)).aestronglyMeasurable
    (.of_forall fun a y _ => by rw [L.norm_map]; exact bd_D _ _ y) (hI 0 (j + 1))
    (.of_forall fun a y _ => ((cd (G a) (j + 1)).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j) y).hasFDerivAt)
  have e := L.toContinuousLinearEquiv.integral_comp_comm (μ := μ) fun a => iteratedFDeriv ℝ (j + 1) (G a) x
  exact h.congr_fderiv e

theorem taylor : HasFTaylorSeriesUpTo ∞ (fun x => ∫ a, G a x ∂μ) fun x j => ∫ a, iteratedFDeriv ℝ j (G a) x ∂μ where
  zero_eq x := ((continuousMultilinearCurryFin0 ℝ V ℂ).toContinuousLinearEquiv.integral_comp_comm (μ := μ)
    fun a => iteratedFDeriv ℝ 0 (G a) x).symm
  fderiv j _ x := deriv_D hG hI j x
  cont j _ := continuous_iff_continuousAt.2 fun x => (deriv_D hG hI j x).continuousAt

theorem eval_int (k j : ℕ) (x : V) :
    (∫ a, J k j (G a) ∂μ) x = ‖x‖ ^ k • iteratedFDeriv ℝ j (fun x => ∫ a, G a x ∂μ) x := by
  rw [← (taylor hG hI).eq_iteratedFDeriv (by exact_mod_cast le_top) x, ← integral_smul]
  exact ((BoundedContinuousFunction.evalCLM ℂ x).integral_comp_comm (int_J hG hI k j)).symm

theorem exists_int : ∃ f : SchwartzMap V ℂ, ∀ k j, J k j f = ∫ a, J k j (G a) ∂μ := by
  refine ⟨⟨fun x => ∫ a, G a x ∂μ, (taylor hG hI).contDiff, fun k j => ⟨‖∫ a, J k j (G a) ∂μ‖, fun x => ?_⟩⟩, fun k j => ?_⟩
  · have := (∫ a, J k j (G a) ∂μ).norm_coe_le_norm x
    rwa [eval_int hG hI, norm_smul, norm_pow, norm_norm] at this
  · ext1 x
    rw [eval_int hG hI]
    rfl

omit hG hI in
theorem factor (T : SchwartzMap V ℂ →L[ℂ] ℂ) : ∃ (s : Finset (ℕ × ℕ))
    (T' : (∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ)) →L[ℂ] ℂ), ∀ f, T f = T' fun i => J i.1.1 i.1.2 f := by
  obtain ⟨s, C, -, h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V ℂ)
    ((normSeminorm ℂ ℂ).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  let j : SchwartzMap V ℂ →ₗ[ℂ] ∀ i : s, V →ᵇ (V [×i.1.2]→L[ℝ] ℂ) := LinearMap.pi fun i => (J i.1.1 i.1.2).toLinearMap
  have hb : ∀ f, ‖T f‖ ≤ C * ‖j f‖ := fun f => by
    refine (h f).trans ?_
    rw [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    refine mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_) C.2
    exact (norm_jet i.1 i.2 f).ge.trans (norm_le_pi_norm (j f) ⟨i, hi⟩)
  have hk : LinearMap.ker j ≤ LinearMap.ker T.toLinearMap := fun f hf => by
    have := hb f
    rw [LinearMap.mem_ker.1 hf, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let t : LinearMap.range j →ₗ[ℂ] ℂ := ((LinearMap.ker j).liftQ T.toLinearMap hk) ∘ₗ j.quotKerEquivRange.symm.toLinearMap
  have ht : ∀ f, t ⟨j f, f, rfl⟩ = T f := fun f => by
    simp only [t, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [j.quotKerEquivRange_symm_apply_image f ⟨f, rfl⟩]
    rfl
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range j) (t.mkContinuous C (by
    rintro ⟨_, f, rfl⟩
    rw [ht]
    exact hb f))
  exact ⟨s, g, fun f => ((hg ⟨j f, f, rfl⟩).trans (ht f)).symm⟩

end SchI

theorem schInt : SchInt := by
  intro V _ _ _ α _ _ _ _ μ G hG hI
  obtain ⟨f, hf⟩ := SchI.exists_int hG hI
  refine ⟨f, fun T => ?_⟩
  obtain ⟨s, T', hT⟩ := SchI.factor T
  have hi : MeasureTheory.Integrable (fun a (i : s) => SchI.J i.1.1 i.1.2 (G a)) μ :=
    MeasureTheory.Integrable.of_eval fun i => SchI.int_J hG hI _ _
  simp only [hT]
  refine ⟨T'.integrable_comp hi, ?_⟩
  rw [T'.integral_comp_comm hi]
  congr 1
  funext i
  rw [hf]
  exact (ContinuousLinearMap.proj (R := ℂ) i).integral_comp_comm hi

end PositivityTheory.ThKCT

end
end

section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

theorem integrable_prod_of_bound {G N : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N] (μ : Measure G) [SFinite μ] (ν : Measure N) [IsFiniteMeasure ν]
    {f : G × N → ℂ} (hf : Continuous f) {K : ℝ} (hK : ∀ u, ∫⁻ g, ‖f (g, u)‖ₑ ∂μ ≤ ENNReal.ofReal K) : Integrable f (μ.prod ν) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod_symm _ hf.enorm.measurable.aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono hK) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem ctFub_of (hU : UnipEx) (hT : ThetaBasic) (hG : GrpTop) (hE : EpsOf) : CTFub := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ hH Φ hΦ ⟨C, k, hb⟩ c hc
  obtain ⟨⟨ν₀, 𝓕₀, a1, a2, a3⟩, ⟨Ω, hΩ, hcov⟩, -⟩ := hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hp.base (Or.inr hp.skew) hH
  obtain ⟨b1, b2, -⟩ := hG F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1
  obtain ⟨-, -, -, -, -, -, -, b3⟩ := hG F E σ hp.base.cm d W.J (hE F E σ B hp.base d W r' s' (Or.inr hp.skew)).1
  obtain ⟨t1, t2, -⟩ := (hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have : IsTopologicalGroup (UA σ X.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have := hp.good.haar
  have : SigmaFinite M.μ := MeasureTheory.sigmaFinite_of_locallyFinite
  have : SFinite (M.μ.restrict M.dom) :=
    @MeasureTheory.instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.Restrict.sigmaFinite M.μ M.dom)
  have key : ∀ (ν : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), ν 𝓕 = 1 → ∀ h, SFinite (ν.restrict 𝓕) ∧
      Integrable (fun x : UA σ X.J × unip σ W H' => theta om Φ x.1 (x.2.1 * h)) ((M.μ.restrict M.dom).prod (ν.restrict 𝓕)) := by
    intro ν 𝓕 h1 h
    have hf : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
    have hcont : Continuous fun u : unip σ W H' => u.1 * h := continuous_subtype_val.mul continuous_const
    obtain ⟨D, hD⟩ := b3 _ (hΩ.image hcont)
    refine ⟨@instSFiniteOfSigmaFinite _ _ _ (IsFiniteMeasure.toSigmaFinite _), integrable_prod_of_bound _ _ (K := |C| * (D : ℝ) ^ k)
      (t1.comp (continuous_fst.prodMk (hcont.comp continuous_snd))) fun u => ?_⟩
    obtain ⟨γ, hγ, hu⟩ := hcov u
    have e : ∀ g, theta om Φ g (u.1 * h) = theta om Φ g ((γ * u).1 * h) := fun g => by
      rw [← t2 1 (one_mem _) γ.1 hγ g, one_mul, Subgroup.coe_mul, mul_assoc]
    simp only [e]
    refine (hb _).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (ht ((γ * u).1 * h) : ℝ) ≤ D := hD _ ⟨_, hu, rfl⟩
    exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h2 k) (by positivity) (abs_nonneg C)
  refine ⟨fun h => ?_, fun ν 𝓕 c1 c2 c3 h => ?_⟩
  · obtain ⟨_, hi⟩ := key ν₀ 𝓕₀ a3 h
    simp only [fun g => hc g ν₀ 𝓕₀ a1 a2 a3 h]
    exact hi.integral_prod_left
  · obtain ⟨_, hi⟩ := key ν 𝓕 c3 h
    simp only [fun g => hc g ν 𝓕 c1 c2 c3 h]
    exact integral_integral_swap (f := fun (g : UA σ X.J) (u : unip σ W H') => theta om Φ g (u.1 * h)) hi

end PositivityTheory.ThKCT
end
end

section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix NNReal
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr
open GlobalTheory.Doubling (absE)

theorem unipEx_of : UnipEx := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH
  obtain ⟨ε, A', h⟩ := isFr hB hY hH
  have G := PositivityTheory.ThKEnd.Grp.unipGood hB.cm (hY.imp (·.herm) (·.skew)) (det_ne hY)
    ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, (h.isUnit_det (det_ne hY).isUnit).ne_zero⟩
  refine ⟨G.ex, G.cov, G.closed, G.right, ?_, fun u hu => ⟨(mem_unip.1 hu).1, ?_⟩, ?_⟩
  · choose m h1 h2 using exists_levi hB.cm h
    let lev : (AE F E)ˣ × UA σ Y₁.J →* UA σ Y.J := MonoidHom.mk' (fun z => m z.1 z.2)
      fun a b => levi_uniq h (h1 _ _) (levi_mul (h1 _ _) (h1 _ _))
    have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
    have c1 : Continuous fun z => mat (lev z) := by
      have e : (fun z => mat (lev z)) = fun z => _ := funext fun z => h2 z.1 z.2
      rw [e]
      refine (continuous_const.matrix_mul (continuous_matrix fun i j => ?_)).matrix_mul continuous_const
      rcases i with i | i <;> rcases j with j | j
      · exact (PositivityTheory.ThKEnd.Grp.continuous_mat.comp continuous_snd).matrix_elem i j
      · exact continuous_const
      · exact continuous_const
      · fin_cases i <;> fin_cases j
        exacts [Units.continuous_val.comp continuous_fst, continuous_const, continuous_const,
          hc.comp (Units.continuous_coe_inv.comp continuous_fst)]
    refine ⟨lev, Continuous.subtype_mk (f := fun z => (lev z).1) (Units.continuous_iff.2 ⟨c1, ?_⟩) _, h1,
      fun t g p hp => levi_uniq h hp (h1 t g)⟩
    have e : (fun z => mat (lev z)⁻¹) = (fun z => mat (lev z)) ∘ fun z => z⁻¹ := funext fun z => by simp
    exact (e ▸ c1.comp continuous_inv : Continuous fun z => mat (lev z)⁻¹)
  · exact h.ad.fix_y (PositivityTheory.ThKG.Tow.Levi.cA_cA hB.cm) u.2 (mem_unip.1 hu).1
  · obtain ⟨t, ht⟩ : ∃ t, absE F E t = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := ⟨_, GlobalTheory.Eis.Conv.absE_halfE F E σ hB.cm⟩
    refine ⟨t⁻¹, ?_⟩
    rw [map_inv, ht, inv_inv, NNReal.coe_pow]
    exact one_lt_pow₀ (by norm_num) Fintype.card_ne_zero

end PositivityTheory.ThKCT

end
end

section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix NNReal
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr

theorem sig_val {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ}
    (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) (u : Fin r ⊕ Fin s → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (A *ᵥ u) =
      ((∑ i, Complex.normSq (u (Sum.inl i)) - ∑ i, Complex.normSq (u (Sum.inr i)) : ℝ) : ℂ) := by
  have e : star (A *ᵥ u) = A.map star *ᵥ star u := funext fun i => RingHom.map_mulVec (starRingEnd ℂ) A u i
  rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
  simp [Matrix.fromBlocks_mulVec, dotProduct, Matrix.neg_mulVec, Complex.mul_conj, sub_eq_add_neg]

theorem aniso {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h0 : min r s = 0) {x : Fin n → ℂ}
    (hx : x ⬝ᵥ M *ᵥ star x = 0) : x = 0 := by
  obtain ⟨hn, A, hA⟩ := h
  obtain ⟨A', -, h1⟩ := PositivityTheory.ThKG.Tow.Pln.frame_inv hn hA
  have e : x = A *ᵥ (A' *ᵥ x) := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  generalize A' *ᵥ x = u at e
  rw [e, sig_val hA, Complex.ofReal_eq_zero] at hx
  have : u = 0 := by
    rcases Nat.min_eq_zero_iff.1 h0 with rfl | rfl
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_sub, neg_eq_zero] at hx
      ext (i | i)
      · exact i.elim0
      · exact Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 hx i (Finset.mem_univ _))
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at hx
      ext (i | i)
      · exact Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 hx i (Finset.mem_univ _))
      · exact i.elim0
  rw [e, this, Matrix.mulVec_zero]

theorem witt_of : Witt := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  refine ⟨fun h0 x hx => ?_, fun n₁ H h1 h2 => ?_⟩
  · obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have e := congrArg (B.emb w).1 hx
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hB.cm.2.2.2, map_zero] at e
    have := aniso (hX.sig w) h0 (x := fun i => (B.emb w).1 (x i)) e
    exact funext fun i => (B.emb w).1.injective ((congrFun this i).trans (map_zero _).symm)
  · obtain ⟨c, hc, hσ⟩ := PositivityTheory.ThKF.exists_scale hB.cm (-1)
    have f : ∀ x, form σ X.J x x = 0 → form σ (c • X.J) x x = 0 := fun x hx => by
      rw [form, Matrix.smul_mulVec, dotProduct_smul]
      exact smul_eq_zero_of_right _ hx
    have key := fun x : IsoV σ X => PositivityTheory.ThKEnd.Grp.wittVec F E σ hB.cm n (c • X.J)
      (fun i j => by simp [hσ, hX.herm])
      (by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc) (det_ne (Or.inl hX))) x.1 H.x x.2.1 h1 (f _ x.2.2) (f _ h2)
    choose g g1 g2 using key
    have g3 : ∀ x, (g x).1ᵀ * X.J * (g x).1.map σ = X.J := fun x => smul_right_injective _ hc (by
      have := g1 x
      rwa [Matrix.mul_smul, Matrix.smul_mul] at this)
    have key : ∀ x, ∃ p : UA σ X.J, mat p = incM F (g x).1 := fun x =>
      PositivityTheory.ThKG.Tow.Levi.exists_UA (g' := incM F (g x)⁻¹.1)
        (by rw [← PositivityTheory.ThKEnd.Grp.incM_mul, Units.mul_inv, PositivityTheory.ThKEnd.Grp.incM_one])
        (by
          conv_rhs => rw [← g3 x]
          rw [PositivityTheory.ThKEnd.Grp.incM_mul, PositivityTheory.ThKEnd.Grp.incM_mul, PositivityTheory.ThKEnd.Grp.incM_conj]
          rfl)
    choose γ hγ using key
    exact ⟨γ, fun x => ⟨mem_ratU.2 ⟨_, hγ x⟩, by rw [hγ, PositivityTheory.ThKEnd.Grp.incM_mulVec, g2]⟩⟩

end PositivityTheory.ThKCT

end
end

section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr PositivityTheory.ThKG.Tow.Pln

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cartan_low {n n₁ : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} {θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ}
    {ι : Matrix (Fin n) (Fin n₁) ℂ} {P : Matrix (Fin n₁) (Fin n) ℂ} (hP : P * ι = 1) (h : IsCartan M θ) (e : θ * ι = ι * θ₁) :
    IsCartan (ιᵀ * M * ι.map star) θ₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← Matrix.one_mul (θ₁ * θ₁), ← hP, Matrix.mul_assoc, ← Matrix.mul_assoc ι, ← e, Matrix.mul_assoc θ, ← e,
      ← Matrix.mul_assoc θ, h1, Matrix.one_mul]
  · have m : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (C : Matrix (Fin b) (Fin c) ℂ),
        (A * C).map star = A.map star * C.map star := fun A C => Matrix.map_mul (f := starRingEnd ℂ)
    calc _ = (ι * θ₁)ᵀ * M * (ι * θ₁).map star := by simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = ιᵀ * (θᵀ * M * θ.map star) * ι.map star := by rw [← e]; simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = _ := by rw [h2]
  · rw [← gram_vec, Matrix.mulVec_mulVec, ← e, ← Matrix.mulVec_mulVec]
    refine h3 _ fun h0 => hx ?_
    rw [← Matrix.one_mulVec x, ← hP, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem splitLat_map {v : Pl F} (τ : E →ₐ[F] Fv F v) {n m : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    {L' : Submodule (𝓞 E) (Fin m → E)} (A : Matrix (Fin m) (Fin n) E) (h : ∀ z ∈ L, A *ᵥ z ∈ L') {w : Fin n → Fv F v}
    (hw : w ∈ splitLat τ L) : A.map τ *ᵥ w ∈ splitLat τ L' :=
  splitLat_le τ ((splitLat τ L').comap ((A.map τ).mulVecLin.restrictScalars _)) (fun z hz => by
    have e : A.map τ *ᵥ (fun i => τ (z i)) = fun i => τ ((A *ᵥ z) i) :=
      funext fun i => (RingHom.map_mulVec (τ : E →+* Fv F v) A z i).symm
    show A.map τ *ᵥ (fun i => τ (z i)) ∈ splitLat τ L'
    rw [e]
    exact map_mem_splitLat τ (h z hz)) hw

theorem low_eps {B : Base F E} (hB : B.IsGood σ) {ε : E} {κ : ℂ} (hκ1 : κ * star κ = 1)
    (hκ : ∀ e : E →+* ℂ, star κ * e ε = κ) {D : Submodule (𝓞 E) E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {H : Plane E n n₁} {i₀ i₁ r s : ℕ} (hY : IsEps σ B ε κ D Y r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) {ε' : E}
    {A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E} (h : IsFr (σ : E →+* E) ε' Y.J Y₁.J H.ι H.x H.y A') :
    1 ≤ r ∧ 1 ≤ s ∧ IsEps σ B ε κ D Y₁ (r - 1) (s - 1) := by
  have hcm := hB.cm
  set P : Matrix (Fin n₁) (Fin n) E := A'.submatrix Sum.inl id with hPd
  have hP : ∀ (u : Fin n₁ → E) (a b : E), P *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = u := fun u a b => funext fun j => by
    have : A' *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = Sum.elim u ![a, b] := by
      rw [← fr_mulVec, Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec]
    exact congrFun this (Sum.inl j)
  have hPι : P * H.ι = 1 := Matrix.ext fun i j => by
    exact (congrFun (congrFun h.inv2 (Sum.inl i)) (Sum.inl j)).trans (by simp [Matrix.one_apply])
  have hform : ∀ u u', form σ Y₁.J u u' = form σ Y.J (H.ι *ᵥ u) (H.ι *ᵥ u') := hH.gram ▸ form_gram Y.J H.ι
  have hL : Y₁.L = Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) := Submodule.ext hH.low
  have cg : ∀ e : E →+* ℂ, (H.ι.map e)ᵀ * (κ • Y.J.map e) * (H.ι.map e).map star = κ • Y₁.J.map e := fun e => by
    rw [Matrix.mul_smul, Matrix.smul_mul, map_gram hcm, hH.gram]
  have hPe : ∀ {S : Type} [CommRing S] (e : E →+* S), P.map e * H.ι.map e = 1 := fun e => by
    rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXX : ∀ e : E →+* ℂ, (fun i => e (H.x i)) ⬝ᵥ (κ • Y.J.map e) *ᵥ star (fun i => e (H.x i)) = 0 := fun e => by
    rw [Matrix.smul_mulVec, dotProduct_smul, ← map_form hcm, hH.xx, map_zero, smul_zero]
  have hmin : min r s ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h1 := aniso (hY.sig w) h0 (hXX _)
    have h2 : H.x = 0 := funext fun i => (B.emb w).1.injective ((congrFun h1 i).trans (map_zero _).symm)
    have e := hH.xy
    rw [h2, form, zero_dotProduct] at e
    exact zero_ne_one e
  refine ⟨by omega, by omega, fun i j => ?_, fun w => ?_, hL ▸ isLattice_comap n n₁ Y.L H.ι P hPι hY.lat, fun u => ?_,
    fun w => ?_, fun v u => ?_⟩
  · rw [← form_single (σ := σ) Y₁.J j i, ← form_single (σ := σ) Y₁.J i j, hform, hform, form_swap hcm hY.herm]
  · rw [← cg]
    refine (real_plane _ (fun i => (B.emb w).1 (H.x i)) (κ • fun i => (B.emb w).1 (H.y i)) _ (P.map (B.emb w).1) hH.rank
      (map_herm hcm _ (hκ _) hY.herm) (hXX _) ?_ ?_ ?_ ?_ (hPe _) (hY.sig w)).1
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.yy, map_zero, smul_zero, smul_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.xy, map_one, smul_eq_mul, smul_eq_mul, mul_one, mul_comm, hκ1]
    · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, map_orth hcm _ Y.J H.ι H.x (fun u => (hH.orth u).1), smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
        map_orth hcm _ Y.J H.ι H.y (fun u => (hH.orth u).2), smul_zero, smul_zero]
  · refine ⟨fun hu u' hu' => ?_, fun G => (hH.low u).2 ((hY.dual _).2 fun z hz => ?_)⟩
    · rw [hform]; exact (hY.dual _).1 ((hH.low u).1 hu) _ ((hH.low u').1 hu')
    · obtain ⟨_, _, u', -, -, hu', hz'⟩ := hH.split z hz
      rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (hH.orth u).1,
        (hH.orth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform]
      exact G u' hu'
  · rw [← cg]
    exact cartan_low (hPe _) (hY.cartan w) (hH.cartan w).1
  · have hn := hH.rank
    let f : Fin n₁ → Fin n := fun j => ⟨skip i₀ i₁ j, by have := j.2; unfold skip; split_ifs <;> omega⟩
    have hf : Function.Injective f := fun a b e => Fin.ext (by
      have := congrArg Fin.val e
      simp only [f, skip] at this
      split_ifs at this <;> omega)
    let T : Matrix (Fin n) (Fin n₁) (Fv F v.1) := (1 : Matrix (Fin n) (Fin n) _).submatrix id f
    have e1 : (Y.bas v).1 * T = H.ι.map (B.τ v) * (Y₁.bas v).1 := Matrix.ext fun a j => by
      rw [← (hH.bas v (f j)).2.2 j rfl a]
      simp [T, Matrix.mul_apply, Matrix.one_apply]
    have e2 : (∀ i, u i ∈ v.1.adicCompletionIntegers F) ↔ ∀ i, (T *ᵥ u) i ∈ v.1.adicCompletionIntegers F := by
      refine ⟨fun G i => sum_mem fun j _ => mul_mem ?_ (G j), fun G j => ?_⟩
      · simp only [T, Matrix.submatrix_apply, Matrix.one_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
      · simpa [T, Matrix.mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using G (f j)
    rw [e2, hY.bas v, Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    refine ⟨fun G => ?_, splitLat_map _ _ fun z hz => (hH.low z).1 hz⟩
    have := splitLat_map (L' := Y₁.L) _ P (fun z hz => by
      obtain ⟨a, b, u', -, -, hu', rfl⟩ := hH.split z hz
      rwa [add_comm (a • H.x), hP]) G
    rwa [Matrix.mulVec_mulVec, show P.map (B.τ v) * H.ι.map (B.τ v) = 1 from hPe (B.τ v : E →+* Fv F v.1),
      Matrix.one_mulVec] at this

theorem low_of : Low := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hH
  refine ⟨fun hY => ?_, fun hY => ?_⟩
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inl hY) hH
    simp only [isHerm_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inr hY) hH
    simp only [isSkew_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h

end PositivityTheory.ThKCT

end
end

section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Euler
open PositivityTheory.ThKG.Tow.Levi (hf hf_apply hf_mulVec iso_of_hf exists_move piInf_incl piInf_cA iso_map_piInf exists_lift exists_inf ad_ext)
open PositivityTheory.ThK (latW KAt)

namespace IwaG

theorem exists_loc {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i j, star (M j i) = M i j) (hθ : IsCartan M θ)
    {v : Fin n → ℂ} (hv0 : v ≠ 0) (hvv : hf M v v = 0) {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g * g' = 1)
    (h2 : gᵀ * M * g.map star = M) :
    ∃ (p p' : Matrix (Fin n) (Fin n) ℂ) (t : ℂ), t ≠ 0 ∧ p * p' = 1 ∧ pᵀ * M * p.map star = M ∧ p *ᵥ v = t • v ∧
      Commute (p' * g) θ := by
  have hd := cartan_det hθ
  obtain ⟨c1, c2, c3⟩ := hθ
  have hgv : g *ᵥ (g' *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  obtain ⟨κ, t, ht, k1, k2, k3⟩ := exists_move hM c1 c2 c3 hv0 (v' := g' *ᵥ v)
    (fun h => hv0 (by rw [← hgv, h, Matrix.mulVec_zero])) hvv (by rw [← h2, ← hf_mulVec, hgv, hvv])
  have hκ : IsUnit κ.det := by
    have e := congrArg Matrix.det k1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at e
    refine IsUnit.mk0 _ fun h => hd ?_
    rw [h, zero_mul, zero_mul] at e
    exact e.symm
  have h1' := mul_eq_one_comm.1 h1
  refine ⟨g * κ, κ⁻¹ * g', t, ht, ?_, iso_of_hf fun x y => ?_, ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc κ, Matrix.mul_nonsing_inv _ hκ, one_mul, h1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf_mulVec, h2, hf_mulVec, k1]
  · rw [← Matrix.mulVec_mulVec, k3, Matrix.mulVec_smul, hgv]
  · rw [mul_assoc, h1', mul_one]
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det κ).2 hκ
    rw [← Matrix.coe_units_inv]
    exact k2.units_inv_left

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n r s : ℕ} {X : Spc F E n} {x : Fin n → E} {v : Pl F}

theorem compFin_smul (u : Pl F) (a : AF F) (z : AE F E) : compFin F E u (a • z) = evFin F u a • compFin F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evFin F u) a b)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem compInf_smul (u : InfinitePlace F) (a : AF F) (z : AE F E) : compInf F E u (a • z) = evInf F u a • compInf F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evInf F u) a b)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def LocIwa (σ : E →ₐ[F] E) (X : Spc F E n) (x : Fin n → E) : Prop :=
  ∀ (v : Pl F) (g : UA σ X.J), g ∈ UAt σ X (evFin F v) → ∃ p ∈ UAt σ X (evFin F v), ∃ k ∈ KAt σ X v, ∃ t : (AE F E)ˣ,
    mat p *ᵥ incV F x = t.1 • incV F x ∧ g = p * k

theorem map_one' {S : Type} [CommRing S] (f : AE F E →+* S) : (1 : Matrix (Fin n) (Fin n) (AE F E)).map f = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem exists_arch (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hx : x ≠ 0) (h0 : form σ X.J x x = 0) (g : UA σ X.J) :
    ∃ (p : UA σ X.J) (t : (AE F E)ˣ), mat p *ᵥ incV F x = t.1 • incV F x ∧
      ∀ w, Commute ((mat (p⁻¹ * g)).map (piInf (B.emb w))) (X.θ w) := by
  have hσ := hB.cm
  choose p p' t ht h1 h2 h3 h4 using fun w => exists_loc (M := X.J.map (B.emb w).1)
    (fun i j => by rw [Matrix.map_apply, ← hσ.2.2.2, hX.herm, Matrix.map_apply]) (hX.cartan w)
    (v := fun i => (B.emb w).1 (x i))
    (fun h => hx (funext fun i => (B.emb w).1.injective ((congrFun h i).trans (map_zero _).symm)))
    (by
      have e := congrArg (B.emb w).1 h0
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ.2.2.2, map_zero] at e
      exact e)
    (g := (mat g).map (piInf (B.emb w))) (g' := (mat g⁻¹).map (piInf (B.emb w)))
    (by rw [← Matrix.map_mul, show mat g * mat g⁻¹ = 1 from g.1.mul_inv, map_one'])
    (by
      rw [← iso_map_piInf (fun τ z => piInf_cA hσ τ z), show (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J from g.2]
      exact Matrix.ext fun i j => piInf_incl _ _)
  obtain ⟨q, q1, q2⟩ := exists_lift hσ B.emb X.J p p' h1 h2
  obtain ⟨a, a1, a2⟩ := exists_inf hσ B.emb t
  obtain ⟨b, b1, b2⟩ := exists_inf hσ B.emb fun w => (t w)⁻¹
  have hab : a * b = 1 := ad_ext hσ B.emb (fun w => by rw [map_mul, a1, b1, mul_inv_cancel₀ (ht w), map_one])
    fun v => by rw [map_mul, a2, b2, mul_one, map_one]
  refine ⟨q, ⟨a, b, hab, (mul_comm _ _).trans hab⟩, funext fun i => ad_ext hσ B.emb (fun w => ?_) fun v => ?_, fun w => ?_⟩
  · have e : piInf (B.emb w) ∘ incV F x = fun i => (B.emb w).1 (x i) := funext fun i => piInf_incl _ _
    rw [RingHom.map_mulVec, q1, e, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, a1]
    exact congrArg _ (congrFun e i).symm
  · rw [RingHom.map_mulVec, q2, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, a2, one_mul]
    rfl
  · have e : (mat q⁻¹).map (piInf (B.emb w)) = p' w := by
      have e1 : (mat q⁻¹).map (piInf (B.emb w)) * p w = 1 := by
        rw [← q1, ← Matrix.map_mul, show mat q⁻¹ * mat q = 1 from q.1.inv_mul, map_one']
      exact left_inv_eq_right_inv e1 (h1 w)
    rw [mat_mul, Matrix.map_mul, e]
    exact h4 w

theorem latW_le : latW X v ≤ latHat X := AddSubgroup.closure_mono (by
  rintro _ ⟨a, ha, hi, y, hy, rfl⟩
  have e : idem v * a = a := at_iff.1 ha
  have := idem_mem hi
  rw [e] at this
  exact ⟨a, this.1, this.2, y, hy, rfl⟩)

theorem idem_latW {z : Fin n → AE F E} (hz : z ∈ latHat X) : idem v • z ∈ latW X v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, hi, y, hy, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨idem v * a, at_iff.2 (by rw [smul_eq_mul, ← mul_assoc, idem_sq]), by
      rw [map_mul, ev_self, one_mul]; exact hi v, y, hy, by rw [smul_smul]; rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact neg_mem ha

theorem int_of_KAt {k : UA σ X.J} (hk : k ∈ KAt σ X v) : IntAt v k := fun z hz h =>
  have h1 : z ∈ latW X v := at_iff.1 h ▸ idem_latW hz
  ⟨latW_le (hk.2 z h1).1, latW_le (hk.2 z h1).2⟩

variable (F) in

def eInf : AF F := ((1, 0) : Ainf F × Af F)

theorem eInf_smul {z : Fin n → AE F E} (hz : z ∈ latHat X) : eInf F • z = 0 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hz
    have h1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
    have : eInf F * a = 0 := Prod.ext ((one_mul a.1).trans h1) (zero_mul a.2)
    rw [smul_smul, this, zero_smul]
  | zero => rw [smul_zero]
  | add a b _ _ ha hb => rw [smul_add, ha, hb, add_zero]
  | neg a _ ha => rw [smul_neg, ha, neg_zero]

theorem glue (hL : X.L.IsLattice E) {z : Fin n → AE F E} (h0 : eInf F • z = 0) (h : ∀ v : Pl F, idem v • z ∈ latHat X) :
    z ∈ latHat X := by
  obtain ⟨m, y, -, hy⟩ := lat_gen (Y := X) hL
  choose a a1 a2 using fun v => (hy _).1 (h v)
  let b : Fin m → AF F := fun i => ((0, ⟨fun v => evFin F v (a v i), Eventually.of_forall fun v => (a1 v i).2 v⟩) : Ainf F × Af F)
  have hb : ∀ v i, evFin F v (b i) = evFin F v (a v i) := fun _ _ => rfl
  refine (hy _).2 ⟨b, fun i => ⟨map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun v => (a1 v i).2 v⟩,
    funext fun j => Supp.adTens_ext (fun w => ?_) fun v => ?_⟩
  · have e := congrArg (compInf F E w) (congrFun h0 j)
    rw [Pi.smul_apply, compInf_smul, show evInf F w (eInf F) = 1 from rfl, one_smul, Pi.zero_apply, map_zero] at e
    rw [e, Finset.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [Pi.smul_apply, compInf_smul, show evInf F w (b i) = 0 from rfl, zero_smul]
  · have e := congrArg (compFin F E v) (congrFun (a2 v) j)
    rw [Pi.smul_apply, compFin_smul, ev_self, one_smul] at e
    rw [← e, Finset.sum_apply, Finset.sum_apply, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, Pi.smul_apply, compFin_smul, compFin_smul, hb]

theorem stab_of_int (hL : X.L.IsLattice E) {A : Matrix (Fin n) (Fin n) (AE F E)}
    (h : ∀ v, ∀ z ∈ latHat X, At (evFin F v) z → A *ᵥ z ∈ latHat X) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    A *ᵥ z ∈ latHat X :=
  glue hL (by rw [← Matrix.mulVec_smul, eInf_smul hz, Matrix.mulVec_zero]) fun v => by
    rw [← Matrix.mulVec_smul]
    exact h v _ (latW_le (idem_latW hz)) (at_iff.2 (by rw [smul_smul, idem_sq]))

theorem piInf_loc {p : UA σ X.J} (hp : p ∈ UAt σ X (evFin F v)) {w : InfinitePlace F} (τ : EmbOver E w) :
    (mat p).map (piInf τ) = 1 := by
  rw [← map_one' (piInf τ)]
  ext i j
  have e : idem v • (mat p - 1) i j = (mat p - 1) i j := congrFun (congrFun (at_iff.1 hp) i) j
  rw [Matrix.map_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, ← Matrix.sub_apply, ← e, piInf,
    RingHom.comp_apply, compInf_smul, show evInf F w (idem v) = 0 from rfl, zero_smul, map_zero]

theorem exists_fin (B : Base F E) (hl : LocIwa σ X x) (S : Finset (Pl F)) :
    ∀ g : UA σ X.J, (∀ v ∉ S, IntAt v g) → ∃ (p : UA σ X.J) (t : (AE F E)ˣ), mat p *ᵥ incV F x = t.1 • incV F x ∧
      (∀ w, (mat p⁻¹).map (piInf (B.emb w)) = 1) ∧ ∀ v, IntAt v (p⁻¹ * g) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact fun g h => ⟨1, 1, by simp [mat_one], fun w => map_one' _, fun v => by simpa using h v (by simp)⟩
  | insert v S hv ih =>
    intro g h
    have hg : prj v g ∈ UAt σ X (evFin F v) := at_iff.2 (cut_eq.1 (congrArg mat (mem_loc.1 (prj_mem g))))
    obtain ⟨p, hp, k, hk, t, ht, e⟩ := hl v _ hg
    have hp' : p⁻¹ ∈ locGrp σ X v := inv_mem (Subgroup.subset_closure hp)
    obtain ⟨q, t', h1, h2, h3⟩ := ih (p⁻¹ * g) fun u hu => by
      by_cases c : u = v
      · subst c
        rw [← int_prj, map_mul, mem_loc.1 hp', e, inv_mul_cancel_left]
        exact int_of_KAt hk
      · exact (int_mul_ne c hp' g).2 (h u (by simp [c, hu]))
    refine ⟨p * q, t' * t, ?_, fun w => ?_, fun u => by rw [mul_inv_rev, mul_assoc]; exact h3 u⟩
    · rw [mat_mul, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, ht, smul_smul, Units.val_mul]
    · rw [mul_inv_rev, mat_mul, Matrix.map_mul, h2, piInf_loc (at_iff.2 (cut_eq.1 (congrArg mat (mem_loc.1 hp')))), mul_one]

theorem iwa_glob {n₁ : ℕ} {H : Plane E n n₁} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hx : H.x ≠ 0)
    (h0 : form σ X.J H.x H.x = 0) (hl : LocIwa σ X H.x) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (g : UA σ X.J) :
    ∃ (p k : UA σ X.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k := by
  obtain ⟨q, t, h1, h2⟩ := exists_arch hB hX hx h0 g
  have hf : ∀ᶠ v in cofinite, IntAt v (q⁻¹ * g) := by
    filter_upwards [ae_mulVec hX.lat (mat (q⁻¹ * g)), ae_mulVec hX.lat (mat (q⁻¹ * g)⁻¹)] with v a b z hz h
    exact ⟨a z hz h, b z hz h⟩
  obtain ⟨p, t', e1, e2, e3⟩ := exists_fin B hl (Set.Finite.toFinset hf) (q⁻¹ * g) fun v hv =>
    not_not.1 fun c => hv ((Set.Finite.mem_toFinset hf).2 c)
  refine ⟨q * p, p⁻¹ * (q⁻¹ * g), t' * t, (hK _).2 ⟨fun w => ?_, fun z hz => ⟨?_, ?_⟩⟩, ?_, by group⟩
  · rw [mat_mul, Matrix.map_mul, e2, one_mul]
    exact h2 w
  · exact stab_of_int hX.lat (fun v z hz h => (e3 v z hz h).1) hz
  · exact stab_of_int hX.lat (fun v z hz h => (e3 v z hz h).2) hz
  · rw [mat_mul, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_smul, h1, smul_smul, Units.val_mul]

end IwaG

end PositivityTheory.ThKCT

end
end

section
noncomputable section

namespace PositivityTheory.ThKCT

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem iwaEx_of (hS : StabEx) : IwaEx := by
  intro F E _ _ _ _ _ σ B n n₁ X r s H hB hX hx h0 K hK
  obtain ⟨K₀, -, -, k1, k2, -⟩ := hS F E σ B n X r s hB hX
  obtain rfl : K = K₀ := Subgroup.ext fun g => (hK g).trans (k1 g).symm
  exact ⟨k2, IwaG.iwa_glob hB hX hx h0 (fun v _ hg => PositivityTheory.ThKG.Loc.Iwa.iwaLoc hB (Or.inl hX) hx h0 v hg) hK⟩

end PositivityTheory.ThKCT

end
end

section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

structure Ext : Prop where
  mixW : MixW
  mixX : MixX
  basic : ThetaBasic
  evZero : EvZero
  evCone : EvCone
  stab : StabEx
  pair : PairEx
  plane : PlaneHerm
  top : GrpTop
  eps : EpsOf
  triple : TriplePair
  weil : WeilConv
  dom : DomWeil
  semi : SoSemi
  decay : SoDecay
  vol : FinVolU
  fin : SoFin

theorem thetaExp : ThetaExp := thetaExp_of slice_of

theorem evUniq : EvUniq := evUniq_of thetaExp

theorem Ext.kernel (h : Ext) : CTKernel :=
  ctKernel_of thetaExp evUniq slice_of evAdm_of h.mixW h.mixX h.basic h.pair low_of unipEx_of h.top h.eps

theorem Ext.fub (h : Ext) : CTFub := ctFub_of unipEx_of h.basic h.top h.eps

theorem Ext.mixAB (h : Ext) : MixAB := Ker.mixAB_of h.mixW h.mixX h.evZero h.pair thetaExp evUniq

theorem Ext.coneA (h : Ext) : ConeA :=
  coneA_of unfold_of unipEx_of stabDec_of h.basic h.top h.eps evAdm_of h.mixAB (lineInt_of slice_of schInt tateAbs) h.dom

theorem Ext.coneB (h : Ext) : ConeB :=
  coneB_of unfold_of unipEx_of stabDec_of h.basic h.top h.eps evAdm_of h.mixAB (lineInt_of slice_of schInt tateAbs) h.semi h.vol h.fin soStab_of
    (soEv_of linEx_of low_of)

theorem Ext.genAniso (h : Ext) : GenAniso := genAniso_of h.kernel h.fub h.mixW h.weil h.basic witt_of h.top h.eps

theorem Ext.genBig (h : Ext) : GenBig := genBig_of h.kernel h.fub h.coneA h.mixW h.weil h.basic witt_of h.top h.eps

theorem Ext.genSmall (h : Ext) : GenSmall :=
  genSmall_of h.kernel h.fub h.coneB (Ker.twoExp_of thetaExp) h.mixAB h.mixW h.evCone witt_of stabDec_of unipEx_of h.basic h.top h.eps
    h.decay h.vol h.fin soStab_of (soZeroA'_of linEx_of h.mixX thetaExp evUniq) (soEv_of linEx_of low_of)

theorem ct_all (h : Ext) : CTKernel ∧ SplitEx ∧ CTBigZero ∧ CTSmallZero ∧ CTBigCone ∧ CTSmallCone :=
  have k := kFinData_of h.stab
  have i := iwaEx_of h.stab
  ⟨h.kernel, splitEx_of h.genBig h.genSmall h.genAniso k h.stab i h.pair h.plane h.evCone h.evZero unipEx_of low_of h.triple,
    ctBigZero_of h.genBig h.genAniso k h.stab i h.pair h.plane h.evCone unipEx_of h.triple,
    ctSmallZero_of h.genAniso k h.stab h.triple, ctBigCone_of h.genBig k i h.pair h.evZero unipEx_of h.triple,
    ctSmallCone_of h.genSmall k i h.pair h.evZero unipEx_of h.triple⟩

end PositivityTheory.ThKCT

end
end
