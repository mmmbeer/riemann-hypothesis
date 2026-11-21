import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveCartierLocalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSectionsLocallyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealPullbackLocallyGenerated
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAndMultiplicityPullbackIsIsoOpen
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAmpleTensorAmplePowProjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArithmeticNefModelOfAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapBijectiveOfIsIsoRestrictStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackCompositionCompatible
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorOfForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfIsIsoRestrictStatement
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorBirationalCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffective

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistBelow

theorem l1 : ∀ (Y : Scheme.{0}) [IsIntegral Y] (J : Y.IdealSheafData), FinalTheorems.EffCartier J → ∃ E : CartierDiv Y, E.Eff ∧ E.supp = J.support ∧ ∀ (y : Y) (U : Y.affineOpens) (f : Γ(Y, U.1)) (hy : y ∈ U.1) (hf : fnOf U.1 (gen_mem hy) f ≠ 0), J.ideal U = Ideal.span {f} → E.IsEqn y (Units.mk0 _ hf) := GlobalTheory.T.effective_cartier_local_equation

theorem l2 : ∀ (X : Scheme.{0}) (M : LB X), M.IsLB → ∀ (I : X.IdealSheafData), IsGloballyGenerated (twist (idealModule I) M) → ∃ (n : ℕ) (σ : Fin n → M.Sec), (∀ (k : Fin n) (i : M.ι) (W : X.affineOpens) (h : W.1 ≤ M.U i), resG X h ((σ k).f i) ∈ I.ideal W) ∧ ∀ (x : X) (i : M.ι) (hx : x ∈ M.U i) (W : X.affineOpens) (hxW : x ∈ W.1) (a : Γ(X, W.1)), a ∈ I.ideal W → X.presheaf.germ W.1 x hxW a ∈ Ideal.span (Set.range fun k => X.presheaf.germ (M.U i) x hx ((σ k).f i)) := GlobalTheory.T.ideal_sections_locally_generated

theorem l3 : ∀ (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData) (y : Y₁) (U : Y₀.Opens) (hx : t y ∈ U) (n : ℕ) (b : Fin n → Γ(Y₀, U)), (∀ (k : Fin n) (W : Y₀.affineOpens) (h : W.1 ≤ U), resG Y₀ h (b k) ∈ I.ideal W) → (∀ (W : Y₀.affineOpens) (hxW : t y ∈ W.1) (a : Γ(Y₀, W.1)), a ∈ I.ideal W → Y₀.presheaf.germ W.1 (t y) hxW a ∈ Ideal.span (Set.range fun k => Y₀.presheaf.germ U (t y) hx (b k))) → ∀ (U' : Y₁.affineOpens) (f : Γ(Y₁, U'.1)) (hyU' : y ∈ U'.1), fnOf U'.1 (gen_mem hyU') f ≠ 0 → (I.comap t).ideal U' = Ideal.span {f} → ∀ (V : Y₁.Opens) (hV : V ≤ t ⁻¹ᵁ U) (hyV : y ∈ V), (∀ k, RegAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f)) ∧ ∃ k, UnitAt y (fnOf V (gen_mem hyV) (t.appLE U V hV (b k)) / fnOf U'.1 (gen_mem hyU') f) := GlobalTheory.T.ideal_pullback_locally_generated

theorem isGenerated_of_sections {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) {n : ℕ}
    (f : Fin n → Y.functionField) (hf : ∀ k, f k ∈ D.sections) (hg : ∀ y, ∃ k, D.GeneratesAt y (f k))
    (P : LB Y) (hP : P.IsLB) (e : cls P hP = toPic D) : IsGenerated P := by
  have h := presents_toLB D
  let s : Fin n → (toLB D).Sec := fun k => h.secEquiv.symm ⟨f k, hf k⟩
  have hs : ∀ k, h.rat (s k) = f k := by
    intro k
    rw [← h.coe_secEquiv]
    simp [s]
  have hgen : IsGenerated (toLB D) := by
    refine ⟨n, s, ?_⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨k, hk⟩ := hg y
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨k, (h.generatesAt_rat_iff (s k)).1 (by rw [hs]; exact hk)⟩
  have hiso : LBIso P (toLB D) := (cls_eq_iff hP (isLB_toLB D)).1 (e.trans h.toPic_eq)
  exact hgen.of_lbIso hP hiso

private theorem fnOf_div_eq_fnOf_div_of_presents {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L : LB X}
    {r : L.ι → (X.functionField)ˣ} (h : Presents D L r) (s : L.Sec) (i j : L.ι)
    (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j) :
    fnOf (L.U i) hi (s.f i) / r i = fnOf (L.U j) hj (s.f j) / r j := by
  have hij : genericPoint X ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  have hr := h.isRatSec i j hij
  have hc := congrArg (fnOf (L.U i ⊓ L.U j) hij) (s.compat i j)
  simp only [map_mul] at hc
  simp only [fnOf, TopCat.Presheaf.germ_res_apply] at hc hr ⊢
  rw [hc, hr]
  have hne : (X.presheaf.germ (L.U i ⊓ L.U j) (genericPoint X) hij).hom
      (L.g i j : Γ(X, L.U i ⊓ L.U j)) ≠ 0 := by
    intro h0
    have := congrArg (fun z => z * (X.presheaf.germ (L.U i ⊓ L.U j) (genericPoint X) hij).hom
      ((L.g i j)⁻¹ : (Γ(X, L.U i ⊓ L.U j))ˣ)) h0
    simp only [zero_mul, ← map_mul, Units.mul_inv, map_one] at this
    exact one_ne_zero this
  rw [mul_div_mul_left _ _ hne]

private theorem Presents_rat_eq_fnOf_div {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L : LB X}
    {r : L.ι → (X.functionField)ˣ} (h : Presents D L r) (s : L.Sec) (j : L.ι)
    (hj : genericPoint X ∈ L.U j) :
    h.rat s = fnOf (L.U j) hj (s.f j) / r j := by
  simp only [Presents.rat, LinearMap.coe_mk, AddHom.coe_mk]
  exact fnOf_div_eq_fnOf_div_of_presents h s _ j _ hj

theorem exists_eff_isGenerated : ∀ (Y₀ Y₁ : Scheme.{0}) [IsNoetherian Y₀] [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData), FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ E : CartierDiv Y₁, E.Eff ∧ E.supp = (I.comap t).support ∧ ∀ᶠ c : ℕ in atTop, ∀ (P : LB Y₁) (hP : P.IsLB), cls P hP = c • CechPic.pull t (cls A hA.isLB) - toPic E → IsGenerated P := by
  intro Y₀ Y₁ _ _ t I hEff A hA
  obtain ⟨E, hEeff, hEsupp, hEq⟩ := l1 Y₁ (I.comap t) hEff
  refine ⟨E, hEeff, hEsupp, ?_⟩
  filter_upwards [hA.eventually_isGloballyGenerated_twist (idealModule I)] with c hc
  intro P hP hcls
  have hM : (lbPow A c).IsLB := isLB_lbPow hA.isLB c
  obtain ⟨n, σ, hσ1, hσ2⟩ := l2 Y₀ (lbPow A c) hM I hc
  have hL : ((lbPow A c).pull t).IsLB := LB.isLB_pull hM t
  have hcov : ∀ y : Y₁, ∃ j, y ∈ ((lbPow A c).pull t).U j := by
    intro y
    have : y ∈ ⨆ i, ((lbPow A c).pull t).U i := by rw [hL.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨i₀, hi₀⟩ := hcov (genericPoint Y₁)
  have h := presents_ofLB hL i₀ hi₀
  have hcls' : cls P hP = toPic (ofLB hL i₀ hi₀ - E) := by
    rw [map_sub, h.toPic_eq, cls_pull hM t, cls_lbPow hA.isLB c, hcls, map_nsmul]
  have key : ∀ y : Y₁, ∃ g : (Y₁.functionField)ˣ, (ofLB hL i₀ hi₀ - E).IsEqn y g ∧
      (∀ k, RegAt y (h.rat (secPull (σ k) t) * g)) ∧ ∃ k, UnitAt y (h.rat (secPull (σ k) t) * g) := by
    intro y
    obtain ⟨j, hj⟩ := hcov y
    have hx : t y ∈ (lbPow A c).U (j PUnit.unit) := Set.mem_iInter.1 hj PUnit.unit
    have hV : ((lbPow A c).pull t).U j ≤ t ⁻¹ᵁ (lbPow A c).U (j PUnit.unit) :=
      fun z hz => Set.mem_iInter.1 hz PUnit.unit
    obtain ⟨U', f, hyU', hfnzd, hspan⟩ := hEff y
    have hf : fnOf U'.1 (gen_mem hyU') f ≠ 0 := by
      haveI : Nonempty U'.1 := ⟨⟨y, hyU'⟩⟩
      intro h0
      rw [← map_zero (fnOf U'.1 (gen_mem hyU'))] at h0
      exact nonZeroDivisors.ne_zero hfnzd (fnOf_injective _ _ h0)
    have hEy := hEq y U' f hyU' hf hspan
    have hDy := (h.isEqn j y hj).sub hEy
    obtain ⟨hreg, hunit⟩ := l3 Y₀ Y₁ t I y ((lbPow A c).U (j PUnit.unit)) hx n
      (fun k => (σ k).f (j PUnit.unit)) (fun k W hW => hσ1 k _ W hW)
      (fun W hxW a ha => hσ2 (t y) _ hx W hxW a ha) U' f hyU' hf hspan _ hV hj
    have hrat : ∀ k, h.rat (secPull (σ k) t) * ↑(frameRat _ i₀ hi₀ j / Units.mk0 _ hf) =
        fnOf _ (gen_mem hj) (Scheme.Hom.appLE t ((lbPow A c).U (j PUnit.unit)) _ hV ((σ k).f (j PUnit.unit))) /
          fnOf U'.1 (gen_mem hyU') f := by
      intro k
      rw [Presents_rat_eq_fnOf_div h _ j (gen_mem hj)]
      have he : fnOf _ (gen_mem hj) ((secPull (σ k) t).f j) =
          fnOf _ (gen_mem hj) (Scheme.Hom.appLE t ((lbPow A c).U (j PUnit.unit)) _ hV ((σ k).f (j PUnit.unit))) := rfl
      rw [he]
      have hr0 : ((frameRat _ i₀ hi₀ j : (Y₁.functionField)ˣ) : Y₁.functionField) ≠ 0 := Units.ne_zero _
      simp only [Units.val_div_eq_div_val, Units.val_mk0]
      field_simp
    exact ⟨_, hDy, fun k => by rw [hrat]; exact hreg k,
      by obtain ⟨k, hk⟩ := hunit; exact ⟨k, by rw [hrat]; exact hk⟩⟩
  apply isGenerated_of_sections (ofLB hL i₀ hi₀ - E) (fun k => h.rat (secPull (σ k) t)) _ _ P hP hcls'
  · intro k
    rw [CartierDiv.mem_sections]
    intro y
    obtain ⟨g, hg, hreg, -⟩ := key y
    exact hg.regularAt_iff.2 (hreg k)
  · intro y
    obtain ⟨g, hg, -, k, hk⟩ := key y
    exact ⟨k, hg.generatesAt_iff.2 hk⟩

end GlobalTheory.TwistBelow
end
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.blowup_ample_minus_exceptional : ∀ (Y₀ Y₁ : Scheme.{0}) [IsNoetherian Y₀] [IsIntegral Y₁] (t : Y₁ ⟶ Y₀) (I : Y₀.IdealSheafData), FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ E : CartierDiv Y₁, E.Eff ∧ E.supp = (I.comap t).support ∧ ∀ᶠ c : ℕ in atTop, ∀ (P : LB Y₁) (hP : P.IsLB), cls P hP = c • CechPic.pull t (cls A hA.isLB) - toPic E → IsGenerated P := by
  atlas_forward_decl _root_.GlobalTheory.TwistBelow.exists_eff_isGenerated
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.PullDiv

theorem compactSpace_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem exists_pullCart_agree : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver (t ≫ q) → ∀ (U : Y₀.Opens), IsIso (t ∣_ U) → ∀ H : CartierDiv Y₁, ∃ H₀ : CartierDiv Y₀, ∀ y : Y₁, t y ∈ U → y ∉ (H - pullCart t H₀).supp := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ hP U hU H
  classical
  have : CompactSpace Y₁ := compactSpace_of_isProjOver hP
  have : Smooth q := SmoothOfRelativeDimension.smooth n q
  have : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n (t ≫ q)

  have hinj : ∀ w₁ w₂ : Y₁, t w₁ ∈ U → t w₂ ∈ U → t w₁ = t w₂ → w₁ = w₂ := by
    intro w₁ w₂ h₁ h₂ e
    have hb : Function.Injective (t ∣_ U) :=
      ((ConcreteCategory.bijective_of_isIso ((t ∣_ U).base))).1
    have := @hb ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ (Subtype.ext ((morphismRestrict_base_coe t U _).trans
      (e.trans (morphismRestrict_base_coe t U ⟨w₂, h₂⟩).symm)))
    exact congrArg Subtype.val this
  let c : Y₀ → ℤ := fun z => if h : ∃ w, t w = z ∧ z ∈ U then H.mult h.choose else 0
  have hc : ∀ w, t w ∈ U → c (t w) = H.mult w := by
    intro w hw
    have h : ∃ w', t w' = t w ∧ t w ∈ U := ⟨w, rfl, hw⟩
    simp only [c, dif_pos h]
    have e := h.choose_spec
    rw [hinj _ _ (by rw [e.1]; exact hw) hw e.1]
  have hsupp : Function.support c ⊆ t '' Function.support H.mult := by
    intro z hz
    by_cases h : ∃ w, t w = z ∧ z ∈ U
    · obtain ⟨w, rfl, hw⟩ := h
      exact ⟨w, by simpa [hc w hw] using hz, rfl⟩
    · exact (hz (by simp only [c]; exact dif_neg h)).elim
  have hfin : (Function.support c).Finite := (H.finite_support_mult.image _).subset hsupp
  have hcod : ∀ z, c z ≠ 0 → Order.coheight z = 1 := by
    intro z hz
    by_cases h : ∃ w, t w = z ∧ z ∈ U
    · obtain ⟨w, rfl, hw⟩ := h
      rw [hc w hw] at hz
      rw [← (GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hU w hw).1]
      exact CartierDiv.coheight_eq_one_of_mult_ne_zero hz
    · exact (hz (by simp only [c]; exact dif_neg h)).elim
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.exists_cartier_with_multiplicities Y₀ (fun x => AbelianProjective.ufd_stalk q x) c hfin hcod
  refine ⟨H₀, fun y hy hmem => ?_⟩
  have : GlobalTheory.IsNormalScheme Y₁ := (isNormalScheme_iff Y₁).mpr fun x =>
    ⟨inferInstance, have := AbelianProjective.ufd_stalk (t ≫ q) x
      UniqueFactorizationMonoid.instIsIntegrallyClosed⟩
  obtain ⟨z, hzy, hz⟩ := ((GlobalTheory.T.cartier_divisor_mult_characterize Y₁ (H - pullCart t H₀)).2.1 y).1 hmem
  have hzU : t z ∈ U := (hzy.map t.continuous).mem_open U.isOpen hy
  apply hz
  have hm := CartierDiv.mult_add (H - pullCart t H₀) (pullCart t H₀) z
  rw [sub_add_cancel, (GlobalTheory.T.coheight_and_multiplicity_pullback_isIso_open Y₀ Y₁ t U hU z hzU).2 H₀, hH₀, hc z hzU] at hm
  omega

end GlobalTheory.PullDiv
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.divisor_agreement_on_isomorphism : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver (t ≫ q) → ∀ (U : Y₀.Opens), IsIso (t ∣_ U) → ∀ H : CartierDiv Y₁, ∃ H₀ : CartierDiv Y₀, ∀ y : Y₁, t y ∈ U → y ∉ (H - pullCart t H₀).supp := by
  atlas_forward_decl _root_.GlobalTheory.PullDiv.exists_pullCart_agree
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Domin

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem mult_zero' (z : X) : (0 : CartierDiv X).mult z = 0 := by
  have h₀ := CartierDiv.mult_add (0 : CartierDiv X) 0 z
  rw [add_zero] at h₀
  omega


theorem eq_of_specializes_of_coheight (z z' : X) (h : z' ⤳ z) (hz : Order.coheight z = 1)
    (hz' : Order.coheight z' = 1) : z' = z := by
  by_cases h' : z' ≤ z
  · exact (h.antisymm h').eq
  · exfalso
    have hlt : z < z' := lt_of_le_not_ge h h'
    have h2 := Order.coheight_strictAnti hlt (by simp [hz'])
    rw [hz, hz'] at h2
    exact lt_irrefl _ h2

end GlobalTheory.Domin

private theorem exists_pow_eq_mul_of_mem_maximalIdeal_dim_le_one {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ringKrullDim R ≤ 1) (a p : R) (ha : a ∈ IsLocalRing.maximalIdeal R) (hp : p ≠ 0) :
    ∃ N : ℕ, ∃ b : R, a ^ N = p * b := by
  by_cases hpu : IsUnit p
  · exact ⟨0, ↑hpu.unit⁻¹, by simp⟩
  · haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by exact_mod_cast hR)
    have hmax : ∀ P : Ideal R, P.IsPrime → p ∈ P → P = IsLocalRing.maximalIdeal R := by
      intro P hP hpP
      rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (⟨P, hP⟩ : PrimeSpectrum R) with h | h
      · have h' := congrArg PrimeSpectrum.asIdeal h
        simp at h'
        rw [h'] at hpP
        exact absurd ((Submodule.mem_bot R).1 hpP) hp
      · have h' := congrArg PrimeSpectrum.asIdeal h
        simpa using h'
    have hrad : a ∈ (Ideal.span {p}).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      rintro P ⟨hPp, hP⟩
      rw [hmax P hP (hPp (Ideal.mem_span_singleton_self p))]
      exact ha
    have hle : Ideal.span {a} ≤ (Ideal.span {p}).radical := (Ideal.span_singleton_le_iff_mem _).2 hrad
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (Submodule.fg_span_singleton a)
    have : a ^ N ∈ Ideal.span {p} := hN (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨N, b, by rw [← hb, mul_comm]⟩

private theorem exists_nsmul_sub_regularAt_of_supp_le {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D E : CartierDiv X) (hE : E.Eff)
    (hsupp : D.supp ≤ E.supp) (z : X) (hz : Order.coheight z = 1) :
    ∃ c0 : ℕ, (z ∉ D.supp → c0 = 0) ∧ ∀ c : ℕ, c0 ≤ c → (c • E - D).RegularAt z 1 := by
  obtain ⟨gD, hgD⟩ := D.exists_isEqn z
  obtain ⟨gE, hgE⟩ := E.exists_isEqn z
  have hEq : ∀ c : ℕ, (c • E - D).IsEqn z (gE ^ c / gD) := fun c => (hgE.nsmul c).sub hgD
  obtain ⟨a, ha⟩ := CartierDiv.eff_iff.1 hE z gE hgE
  suffices key : ∃ c0 : ℕ, (z ∉ D.supp → c0 = 0) ∧ ∀ c : ℕ, c0 ≤ c → RegAt z ((gE ^ c / gD : (X.functionField)ˣ) : X.functionField) by
    obtain ⟨c0, h0, hc0⟩ := key
    exact ⟨c0, h0, fun c hc => (hEq c).regularAt_iff.2 (by rw [one_mul]; exact hc0 c hc)⟩
  by_cases hzD : z ∈ D.supp
  · have ha' : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hau
      exact (hgE.mem_supp_iff.1 (hsupp hzD)) ⟨a, hau, ha⟩
    obtain ⟨⟨q, ⟨p, hp⟩⟩, hpq⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (X.presheaf.stalk z))
      ((gD⁻¹ : (X.functionField)ˣ) : X.functionField)
    dsimp only at hpq
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    have hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1 := (ringKrullDim_stalk_le_one_iff z).2 hz.le
    obtain ⟨N, b, hab⟩ := exists_pow_eq_mul_of_mem_maximalIdeal_dim_le_one hdim a p ha' hp0
    refine ⟨N, fun h => absurd hzD h, fun c hc => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
    refine ⟨b * q * a ^ d, ?_⟩
    have hpK : algebraMap (X.presheaf.stalk z) X.functionField p ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, ← ha, div_eq_mul_inv,
      ← Units.val_inv_eq_inv_val, ← hpq, IsFractionRing.mk'_eq_div, ← map_pow, pow_add, hab]
    simp only [map_mul]
    field_simp
  · have hu : UnitAt z (gD : X.functionField) := by
      by_contra h
      exact hzD (hgD.mem_supp_iff.2 h)
    obtain ⟨u, hu, hugD⟩ := hu
    refine ⟨0, fun _ => rfl, fun c _ => ⟨a ^ c * ↑hu.unit⁻¹, ?_⟩⟩
    have h1 : algebraMap (X.presheaf.stalk z) X.functionField u *
        algebraMap (X.presheaf.stalk z) X.functionField (↑hu.unit⁻¹) = 1 := by
      rw [← map_mul]; simp
    have hne := left_ne_zero_of_mul_eq_one h1
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, ← ha, ← hugD, map_mul, map_pow,
      eq_div_iff hne, mul_assoc, mul_comm (algebraMap _ _ _) (algebraMap _ _ u), h1, mul_one]

private theorem eq_of_mem_supp_specializes_coheight_one {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (y z : X) (hy : y ∈ D.supp) (h : y ⤳ z)
    (hz : Order.coheight z = 1) : y = z := by
  by_contra hne
  have hzy : z ≤ y := h
  have hnot : ¬ y ≤ z := fun h' => hne (h.antisymm h').eq
  have hlt : z < y := lt_of_le_not_ge hzy hnot
  have hfin : Order.coheight y < ⊤ := lt_of_le_of_lt (Order.coheight_anti hzy) (by simp [hz])
  have h1 := Order.coheight_strictAnti hlt hfin
  rw [hz] at h1
  have h0 : Order.coheight y = 0 := ENat.lt_one_iff_eq_zero.1 h1
  have hη : genericPoint X ⤳ y := genericPoint_specializes y
  by_cases hyη : genericPoint X ≤ y
  · have hyeq : y = genericPoint X := (Specializes.antisymm hyη hη).eq
    exact D.genericPoint_notMem_supp (hyeq ▸ hy)
  · have hlt2 : y < genericPoint X := lt_of_le_not_ge hη hyη
    have h2 := Order.coheight_strictAnti hlt2 (lt_of_le_of_lt (Order.coheight_anti (show y ≤ genericPoint X from hη)) (by simp [h0]))
    rw [h0] at h2
    exact absurd h2 (by simp)

private theorem finite_coheight_one_inter_supp {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] (D : CartierDiv X) :
    {z : X | Order.coheight z = 1 ∧ z ∈ D.supp}.Finite := by
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨S, hSirr, hSeq⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible D.supp
  refine Set.Finite.subset (S.finite_toSet.biUnion fun k _ => (show {x : X | IsGenericPoint x (k : Set X)}.Subsingleton
    from fun x hx y hy => hx.eq hy).finite) ?_
  rintro z ⟨hz, hzD⟩
  have hzS : z ∈ (S.sup id : TopologicalSpace.Closeds X) := by rw [← hSeq]; exact hzD
  have hex : z ∈ (S.sup id : TopologicalSpace.Closeds X) → ∃ k ∈ S, z ∈ k :=
    Finset.sup_induction (p := fun C : TopologicalSpace.Closeds X => z ∈ C → ∃ k ∈ S, z ∈ k)
      (fun h => by rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot] at h; exact absurd h (Set.notMem_empty z))
      (fun a ha b hb h => by
        rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_sup] at h
        rcases h with h | h
        exacts [ha h, hb h])
      (fun k hk h => ⟨k, hk, h⟩)
  obtain ⟨k, hkS, hzk⟩ := hex hzS
  have hirr := hSirr ⟨k, hkS⟩
  have ht : IsGenericPoint hirr.genericPoint (k : Set X) := hirr.isGenericPoint_genericPoint k.isClosed
  have hkD : (k : Set X) ⊆ D.supp := by
    have : k ≤ D.supp := by rw [hSeq]; exact Finset.le_sup (f := id) hkS
    exact this
  have hteq := eq_of_mem_supp_specializes_coheight_one D _ z (hkD ht.mem) (ht.specializes hzk) hz
  exact Set.mem_biUnion hkS (show IsGenericPoint z (k : Set X) from hteq ▸ ht)

open GlobalTheory.Domin in

theorem GlobalTheory.effDominates : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [CompactSpace X] (D E : CartierDiv X), E.Eff → D.supp ≤ E.supp → ∃ c : ℕ, (c • E - D).Eff := by
  intro X _ _ _ _ D E hE hsupp
  classical
  have hfin := finite_coheight_one_inter_supp D
  let c0 : X → ℕ := fun z =>
    if hz : Order.coheight z = 1 then Classical.choose (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz) else 0
  refine ⟨hfin.toFinset.sup c0, ?_⟩
  have hreg : ∀ z : X, Order.coheight z = 1 → (hfin.toFinset.sup c0 • E - D).RegularAt z 1 := by
    intro z hz
    have hspec := Classical.choose_spec (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz)
    apply hspec.2
    have hc0 : c0 z = Classical.choose (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz) := by simp [c0, hz]
    rw [← hc0]
    by_cases hzD : z ∈ D.supp
    · exact Finset.le_sup (f := c0) (hfin.mem_toFinset.2 ⟨hz, hzD⟩)
    · rw [hc0, hspec.1 hzD]
      exact Nat.zero_le _
  intro x
  obtain ⟨g, hg⟩ := (hfin.toFinset.sup c0 • E - D).exists_isEqn x
  rw [hg.regularAt_iff, one_mul]
  apply regAt_of_forall_coheight_eq_one
  intro z hzx hz
  obtain ⟨U, hxU, hU⟩ := hg.exists_nhds
  have hgz := hU z (hzx.mem_open U.isOpen hxU)
  have h1 := hgz.regularAt_iff.1 (hreg z hz)
  rwa [one_mul] at h1
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.effective_multiple_dominates : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [CompactSpace X] (D E : CartierDiv X), E.Eff → D.supp ≤ E.supp → ∃ c : ℕ, (c • E - D).Eff := by
  atlas_forward_decl _root_.GlobalTheory.effDominates
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.AmpleUpstairs

open GlobalTheory.Cartier.CartierDiv in

theorem supp_neg_le {X : Scheme.{0}} [IsIntegral X] (D : GlobalTheory.Cartier.CartierDiv X) : (-D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [hg.neg.mem_supp_iff] at hx
  rw [hg.mem_supp_iff]
  intro hu
  apply hx
  rw [Units.val_inv_eq_inv_val]
  exact hu.inv

open GlobalTheory.Cartier.CartierDiv in

theorem supp_nsmul_le {X : Scheme.{0}} [IsIntegral X] (D : GlobalTheory.Cartier.CartierDiv X) (m : ℕ) :
    (m • D).supp ≤ D.supp := by
  intro x hx
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  rw [(hg.nsmul m).mem_supp_iff] at hx
  rw [hg.mem_supp_iff]
  intro hu
  apply hx
  rw [Units.val_pow_eq_pow_val]
  have key : ∀ j : ℕ, UnitAt x ((g : X.functionField) ^ j) := by
    intro j
    induction j with
    | zero => simpa using unitAt_one x
    | succ j ih => rw [pow_succ]; exact ih.mul hu
  exact key m

end GlobalTheory.AmpleUpstairs

namespace GlobalTheory

open GlobalTheory.AmpleUpstairs in

theorem exists_ample_pull_sub_eff : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver q → IsProjOver (t ≫ q) → ∀ I : Y₀.IdealSheafData, IsIso (t ∣_ I.support.compl) → FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (c : ℕ) (E : CartierDiv Y₁) (A₁ : LB Y₁) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ (I.comap t).support ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  intro k _ _ Y₀ Y₁ _ _ _ _ q n t _ _ _ hq ht I hiso hI A hA
  obtain ⟨-, L₁, hL₁⟩ := isProper_and_exists_isAmpleLB_of_isProjOver ht
  haveI : CompactSpace Y₁ := hL₁.compactSpace
  haveI : CompactSpace Y₀ := hA.compactSpace
  haveI : IsNoetherian Y₀ := {}
  haveI : Smooth (t ≫ q) := SmoothOfRelativeDimension.smooth n _
  haveI : GlobalTheory.IsNormalScheme Y₁ := GlobalTheory.ModifSections.isNormalScheme_of_smooth (t ≫ q)
  obtain ⟨H, hH⟩ := toPic_surjective (cls L₁ hL₁.isLB)
  obtain ⟨H₀, hH₀⟩ := GlobalTheory.T.divisor_agreement_on_isomorphism k Y₀ Y₁ q n t ht I.support.compl hiso H
  obtain ⟨E₀, hE₀, hsE₀, hgen⟩ := GlobalTheory.T.blowup_ample_minus_exceptional Y₀ Y₁ t I hI A hA
  have hD : (H - pullCart t H₀).supp ≤ E₀.supp := by
    intro y hy
    rw [hsE₀, Scheme.IdealSheafData.support_comap]
    by_contra h
    exact hH₀ y h hy
  obtain ⟨e, he⟩ := GlobalTheory.T.effective_multiple_dominates Y₁ (H - pullCart t H₀) E₀ hE₀ hD
  obtain ⟨c₁, hc₁, hc₁'⟩ :=
    ((hA.eventually_isGenerated_tens_lbPow (isLB_toLB (-H₀))).and (eventually_ge_atTop 1)).exists
  obtain ⟨c₂, hc₂⟩ := hgen.exists
  obtain ⟨P, hP, hPc⟩ := cls_surj (c₂ • CechPic.pull t (cls A hA.isLB) - toPic E₀)
  have gP := hc₂ P hP hPc
  have g₁ := hc₁.pull t
  have gM := AmpleModelPos.isGenerated_tens g₁ (gP.pow e)
  have hA₁L := isLB_tens hL₁.isLB gM.isLB
  have hA₁ : IsAmpleLB (tens L₁ (tens ((tens (toLB (-H₀)) (lbPow A c₁)).pull t) (lbPow P e))) := by
    refine hL₁.tensor_isGenerated gM hA₁L ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hA₁L hL₁.isLB) gM.isLB)).1 ?_)
    rw [cls_div (LB.isLB_div hA₁L hL₁.isLB) gM.isLB, cls_div hA₁L hL₁.isLB, cls_tens hL₁.isLB gM.isLB]
    abel
  refine ⟨c₁ + e * c₂, e • E₀ - (H - pullCart t H₀), _, hA₁, by omega, he, ?_, ?_⟩
  · rw [sub_eq_add_neg]
    refine (GlobalTheory.Cartier.CartierDiv.supp_add_le _ _).trans (sup_le ((supp_nsmul_le _ _).trans hsE₀.le) ?_)
    exact (supp_neg_le _).trans (hD.trans hsE₀.le)
  · rw [cls_tens hL₁.isLB gM.isLB, cls_tens g₁.isLB (gP.pow e).isLB,
      cls_lbPow hP e, hPc, cls_pull (isLB_tens (isLB_toLB (-H₀)) (isLB_lbPow hA.isLB c₁)) t,
      cls_tens (isLB_toLB (-H₀)) (isLB_lbPow hA.isLB c₁), cls_lbPow hA.isLB c₁, ← toPic_apply,
      map_sub, map_nsmul, map_sub, toPic_pullCart, hH, map_add, map_neg, map_nsmul, add_smul, mul_smul]
    simp only [map_neg, smul_sub]
    abel

end GlobalTheory
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.blowup_ample_relative : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver q → IsProjOver (t ≫ q) → ∀ I : Y₀.IdealSheafData, IsIso (t ∣_ I.support.compl) → FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (c : ℕ) (E : CartierDiv Y₁) (A₁ : LB Y₁) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ (I.comap t).support ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  atlas_forward_decl _root_.GlobalTheory.exists_ample_pull_sub_eff
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.pullback_composition_compatible : ∀ (k : Type) [Field k] (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (t : Z ⟶ Y) [IsDominant t], functionFieldMap (t ≫ s) = (functionFieldMap t).comp (functionFieldMap s) ∧ (∀ D : CartierDiv X, pullCart (t ≫ s) D = pullCart t (pullCart s D)) ∧ ∀ (n : ℕ) (η : RatForms p n) (K : CartierDiv Z), IsDivOfForm K (EtaleKlt.ratPull p (t ≫ s) n η) ↔ IsDivOfForm K (EtaleKlt.ratPull (s ≫ p) t n (EtaleKlt.ratPull p s n η)) := by
  first | exact @_root_.GlobalTheory.Discrepancy.pull_comp | exact _root_.GlobalTheory.Discrepancy.pull_comp | (intros; apply _root_.GlobalTheory.Discrepancy.pull_comp <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.canonical_divisor_birational_compare : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)] (U : Y₀.Opens), (U : Set Y₀).Nonempty → IsIso (t ∣_ U) → ∀ (η : RatForms q n), η ≠ 0 → ∀ (K₀ : CartierDiv Y₀) (K₁ : CartierDiv Y₁), IsDivOfForm K₀ η → IsDivOfForm K₁ (EtaleKlt.ratPull q t n η) → ∀ y : Y₁, t y ∈ U → y ∉ (K₁ - pullCart t K₀).supp := by
  first | exact @_root_.GlobalTheory.Discrepancy.CanonIso.not_mem_supp_sub_pullCart | exact _root_.GlobalTheory.Discrepancy.CanonIso.not_mem_supp_sub_pullCart | (intros; apply _root_.GlobalTheory.Discrepancy.CanonIso.not_mem_supp_sub_pullCart <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogResStep

open GlobalTheory.Cartier.CartierDiv in

theorem supp_neg_le {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) : (-D).supp ≤ D.supp := fun x hx h =>
  hx (by simpa using h.neg)

theorem supp_nsmul_le {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (m : ℕ) : (m • D).supp ≤ D.supp := by
  induction m with
  | zero => simp [(CartierDiv.supp_eq_bot_iff (D := (0 : CartierDiv X))).2 rfl]
  | succ m ih => exact (succ_nsmul D m ▸ CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

theorem sup_ne_top {Y : Scheme.{0}} [IsIntegral Y] {Z W : Closeds Y} (hZ : Z ≠ ⊤) (hW : W ≠ ⊤) : Z ⊔ W ≠ ⊤ := by
  have key : ∀ C : Closeds Y, C ≠ ⊤ → genericPoint Y ∉ C := fun C hC h => hC <| by
    ext x; simp only [Closeds.coe_top, Set.mem_univ, iff_true]
    exact ((genericPoint_spec Y).mem_closed_set_iff C.isClosed).1 h (Set.mem_univ x)
  intro h
  have : genericPoint Y ∈ Z ⊔ W := by rw [h]; trivial
  rcases this with h' | h'
  · exact key Z hZ h'
  · exact key W hW h'

end GlobalTheory.LogResStep

open GlobalTheory.LogResStep in
theorem GlobalTheory.exists_logRes_ample : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), η ≠ 0 → ∀ (Y₀ : Scheme.{0}) [IsIntegral Y₀] (s₀ : Y₀ ⟶ X) [IsDominant s₀], SmoothOfRelativeDimension n (s₀ ≫ p) → IsProjOver (s₀ ≫ p) → Function.Bijective (functionFieldMap s₀) → ∀ (Z : Closeds Y₀), Z ≠ ⊤ → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (t : Y ⟶ Y₀) (_ : IsDominant t) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G (t ≫ s₀) K B ∧ (∀ y, t y ∈ Z → y ∈ B) ∧ ∃ (c : ℕ) (E : CartierDiv Y) (A₁ : LB Y) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ B ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  intro hP k _ _ X _ p n η m G hη Y₀ _ s₀ _ hsm hproj hbij Z hZ A hA
  haveI : SmoothOfRelativeDimension n (s₀ ≫ p) := hsm
  haveI : Smooth (s₀ ≫ p) := SmoothOfRelativeDimension.smooth n _
  haveI : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian (s₀ ≫ p)

  set η₀ := EtaleKlt.ratPull p s₀ n η with hη₀def
  have hη₀ : η₀ ≠ 0 := fun h =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y₀ p s₀ hbij n).1 (h.trans (map_zero _).symm))
  obtain ⟨K₀, hK₀⟩ := (GlobalTheory.T.canonical_divisor_of_form k Y₀ (s₀ ≫ p) n η₀ hη₀).1

  set D₀ : CartierDiv Y₀ := pullCart s₀ G - m • K₀ with hD₀
  set Z' : Closeds Y₀ := Z ⊔ D₀.supp with hZ'
  have hZ'top : Z' ≠ ⊤ := sup_ne_top hZ D₀.supp_ne_top
  set I : Y₀.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z' with hIdef
  have hIsupp : (I.support : Set Y₀) = Z' := Scheme.IdealSheafData.coe_support_vanishingIdeal Z'
  have hI : I ≠ ⊥ := by
    intro h
    apply hZ'top
    ext x
    rw [← hIsupp, h]
    simp
  obtain ⟨Y, t, hYi, hsmY, hprojY, -, hiso, heff, hsnc⟩ := hP k n Y₀ (s₀ ≫ p) inferInstance hsm hproj I hI
  haveI := hYi
  have hne := Principalise.nonempty_compl_support hI
  haveI : IsDominant t := GlobalTheory.T.isDominant_of_isIso_restrict' Y₀ Y t I.support.compl hne hiso
  haveI : SmoothOfRelativeDimension n (t ≫ s₀ ≫ p) := hsmY
  haveI : SmoothOfRelativeDimension n ((t ≫ s₀) ≫ p) := by rw [Category.assoc]; exact hsmY
  haveI : Smooth (t ≫ s₀ ≫ p) := SmoothOfRelativeDimension.smooth n _
  have hsmY' : SmoothOfRelativeDimension n ((t ≫ s₀) ≫ p) := by rw [Category.assoc]; exact hsmY
  have hprojY' : IsProjOver ((t ≫ s₀) ≫ p) := by rw [Category.assoc]; exact hprojY
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (t ≫ s₀ ≫ p)
  have hcomp := GlobalTheory.T.pullback_composition_compatible k X Y₀ Y p s₀ t
  have hbt := GlobalTheory.T.functionFieldMap_bijective_of_isIso_restrict' Y₀ Y t I.support.compl hne hiso
  have hbij' : Function.Bijective (functionFieldMap (t ≫ s₀)) := by
    rw [hcomp.1, RingHom.coe_comp]; exact hbt.comp hbij
  have hη₁ : EtaleKlt.ratPull p (t ≫ s₀) n η ≠ 0 := fun h =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational k X Y p (t ≫ s₀) hbij' n).1 (h.trans (map_zero _).symm))
  obtain ⟨K, hK⟩ := (GlobalTheory.T.canonical_divisor_of_form k Y ((t ≫ s₀) ≫ p) n _ hη₁).1
  have hK' : IsDivOfForm K (EtaleKlt.ratPull (s₀ ≫ p) t n η₀) := ((hcomp.2.2 n η K).1 hK)

  have hB : ∀ y : Y, y ∈ (I.comap t).support ↔ t y ∈ Z' := fun y => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap]
    change t y ∈ (I.support : Set Y₀) ↔ _
    rw [hIsupp]; rfl
  have hkiso := GlobalTheory.T.canonical_divisor_birational_compare k Y₀ Y (s₀ ≫ p) n t I.support.compl hne hiso η₀ hη₀ K₀ K hK₀ hK'
  have heq : pullCart (t ≫ s₀) G - m • K = pullCart t D₀ + m • (-(K - pullCart t K₀)) := by
    rw [hcomp.2.1 G, hD₀]
    change _ = pullCartHom t (pullCart s₀ G - m • K₀) + _
    rw [map_sub, map_nsmul]
    change _ = pullCart t (pullCart s₀ G) - m • pullCart t K₀ + _
    rw [smul_neg, nsmul_sub]; abel
  refine ⟨Y, hYi, t, inferInstance, K, (I.comap t).support,
    ⟨hsmY', hprojY', hbij', hK, hsnc, ?_⟩, ?_, ?_⟩
  · rw [heq]
    refine (CartierDiv.supp_add_le _ _).trans (sup_le ?_ ?_)
    · intro y hy
      rw [hB]
      exact Or.inr ((GlobalTheory.T.cartierDivisorPullback_support_and_effective Y₀ Y t D₀).1 y hy)
    · intro y hy
      have hy' := supp_neg_le _ (supp_nsmul_le _ m hy)
      rw [hB]
      by_contra hc
      refine hkiso y ?_ hy'
      intro hm
      have : t y ∈ (I.support : Set Y₀) := hm
      rw [hIsupp] at this; exact hc this
  · intro y hy; rw [hB]; exact Or.inl hy
  · exact GlobalTheory.T.blowup_ample_relative k Y₀ Y (s₀ ≫ p) n t hproj hprojY I hiso heff A hA
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_embedded_resolution : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), η ≠ 0 → ∀ (Y₀ : Scheme.{0}) [IsIntegral Y₀] (s₀ : Y₀ ⟶ X) [IsDominant s₀], SmoothOfRelativeDimension n (s₀ ≫ p) → IsProjOver (s₀ ≫ p) → Function.Bijective (functionFieldMap s₀) → ∀ (Z : Closeds Y₀), Z ≠ ⊤ → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (t : Y ⟶ Y₀) (_ : IsDominant t) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G (t ≫ s₀) K B ∧ (∀ y, t y ∈ Z → y ∈ B) ∧ ∃ (c : ℕ) (E : CartierDiv Y) (A₁ : LB Y) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ B ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  atlas_forward_decl _root_.GlobalTheory.exists_logRes_ample
end
