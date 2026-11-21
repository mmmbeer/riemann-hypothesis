import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsSMulRegularNatCast
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtOmPHtEval
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHTLatOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlgOfFlagClSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagAtOfFlagAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLatFlagsOfAllSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLBLatLBAndTrAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatChartTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanImageOfIsCompl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFormEqOneAddMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimFlags
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBigCellIffCellDiscNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenBigCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFrameBigCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineHyperplaneCut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRTensorRangeTensorAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TmulEqZeroOfMemSmulTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeAdjoint

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam

namespace GlobalTheory.LocM

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem Mdl.isUnit_natCast_of_le_genO (B : Mdl Y i₀) {V : B.X.Opens} (hV : V ≤ B.genO) : IsUnit ((p : ℕ) : Γ(B.X, V)) := by
  have := (B.X.toRingedSpace.isUnit_res_basicOpen ((p : ℕ) : Γ(B.X, ⊤))).map (B.X.presheaf.map (homOfLE hV).op).hom
  exact (map_natCast ((B.X.presheaf.map (homOfLE hV).op).hom.comp
    (B.X.presheaf.map (homOfLE (B.X.basicOpen_le _)).op).hom) p) ▸ this

theorem HTm.omP_sec_eq_top {Z : Mdl Y i₀} {n : ℕ} (h : HTm.HTOn Z n) {V : Z.X.Opens} (hV : V ≤ Z.genO) :
    (HTm.omP h).sec V = ⊤ := eq_top_iff.2 fun s _ => by
  obtain ⟨u, hu⟩ := (Z.isUnit_natCast_of_le_genO hV).pow n
  have := HTm.pow_smul_mem_omP h ((↑u⁻¹ : Γ(Z.X, V)) • s)
  rwa [← Nat.cast_smul_eq_nsmul Γ(Z.X, V), Nat.cast_pow, ← hu, smul_smul, Units.mul_inv, one_smul] at this

variable {P : ∀ B : Mdl Y i₀, Lat B → Prop} {Z Z' : Mdl Y i₀}

theorem Step.admitted.of_isMap {t : Step Y i₀} (h : t.admitted P Z) {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) : t.admitted P Z' := by
  refine ⟨.inr ?_, h.2⟩
  obtain rfl | ⟨g, hg⟩ := h.1
  exacts [⟨f, hf⟩, ⟨f ≫ g, MapComp.isMap_comp hf hg⟩]

namespace FlagFam

def single (t : Step Y i₀) (h : t.admitted P Z) : FlagFam P Z := ⟨{t}, fun _ ht => Finset.mem_singleton.1 ht ▸ h⟩

open Classical in

def union (s s' : FlagFam P Z) : FlagFam P Z := ⟨s.1 ∪ s'.1, fun t ht => (Finset.mem_union.1 ht).elim (s.2 t) (s'.2 t)⟩

theorem mem_union {s s' : FlagFam P Z} {t : Step Y i₀} : t ∈ (s.union s').1 ↔ t ∈ s.1 ∨ t ∈ s'.1 := by
  classical
  exact Finset.mem_union

def pull (s : FlagFam P Z) {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) : FlagFam P Z' := ⟨s.1, fun t ht => (s.2 t ht).of_isMap hf⟩

end FlagFam

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

def flgTrue : FlgSt ct := flgOf ct (IsHTLatOf (htmTrue ct))

theorem isFlagCl_flgTrue (Z : ct.Mdl) (s : (flgTrue ct).FlagData Z) : IsFlagCl Z s.1 ((flgTrue ct).flagCl Z s) :=
  flgOf_flagCl_spec D A N j S κ p ct _ Z s

namespace HTm

variable {ct} {Z : ct.Mdl}

theorem isHTLatOf_iff {L : Lat Z} : IsHTLatOf (htmTrue ct) Z L ↔
    (∃ n, IsHTBlowup ct Z (ct.Xn n)) ∧ ∀ y : ct.Pt Z, latAt ct y (omSub ct Z) = latAt ct y L.N :=
  and_congr_left' (exists_congr fun _ => and_iff_right_of_imp fun H => ((isHTBlowup_iff ct).1 H).choose_spec.1)

variable (ct Z) in

def OmFree : Prop := ∀ x : Z.X, ∃ (V : Z.X.Opens) (r : ℕ) (m : Fin r → Γ((omSub ct Z).toMod, V)), x ∈ V ∧ VB.IsFrame m

def omLat (hf : OmFree ct Z) : Lat Z where
  N := omSub ct Z
  free := hf
  gen _ hV := omP_sec_eq_top _ hV

variable (ct Z) in

def htFam : (flgTrue ct).FlagData Z := classFam (IsHTLatOf (htmTrue ct)) Z

end HTm

example : (flgTrue ct).flagCl ct.Xm (flgTrue ct).allFlags = ct.YY := (flgTrue ct).YY_eq.symm

example (Z : ct.Mdl) : (flgTrue ct).flagCl Z (FlagFam.empty Z) = Z := ct.flagCl_empty Z

example (σ : D.host.E →+* ℂ) (k : ℕ) (hk : k ≤ S.Dw.mult σ) :
    ((flgTrue ct).flagCl ct.Xm (FlagFam.single ⟨ct.Xm, Lat.top _, σ, k, hk⟩ ⟨.inl rfl, .inl Lat.isTop_top⟩)).ty σ = {k} := by
  refine ((isFlagCl_flgTrue ct _ _).2.1 σ).trans ?_
  rw [show ct.Xm.ty σ = ∅ from ct.B.ty none σ]
  ext r
  simp [mem_stepTy, FlagFam.single, eq_comm]

example (Z : ct.Mdl) (h : ¬ ∃ n, HTm.IsHTBlowup ct Z (ct.Xn n)) : ∃ hf : HTm.OmFree ct Z, HTm.omLat hf = Lat.top Z := by
  have e : HTm.htData ct Z = ⟨0, 0⟩ := dif_neg fun ⟨d, hd⟩ => h ⟨d.1, (HTm.isHTBlowup_iff ct).2 ⟨d.2, hd⟩⟩
  have k : ∀ V, (HTm.omSub ct Z).sec V = (Lat.top Z).N.sec V := fun V => by
    rw [Lat.isTop_top V, HTm.omSub, e, eq_top_iff]
    exact fun s _ => by simpa using HTm.pow_smul_mem_omP (0 : HTm.HTOn Z 0) s
  have k' : HTm.omSub ct Z = (Lat.top Z).N := by
    generalize HTm.omSub ct Z = M, (Lat.top Z).N = M' at k
    cases M; cases M'; obtain rfl := funext k; rfl
  exact ⟨by rw [HTm.OmFree, k']; exact (Lat.top Z).free, Lat.ext k⟩

example (Z : ct.Mdl) (h : ¬ ∃ n, HTm.IsHTBlowup ct Z (ct.Xn n)) (L : Lat Z) : ¬ IsHTLatOf (htmTrue ct) Z L :=
  fun hL => h (HTm.isHTLatOf_iff.1 hL).1

end GlobalTheory.LocM
end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.EigenSplit GlobalTheory.FlagPts GlobalTheory.TotalFrame
open GlobalTheory.CechPic (cls)

namespace GlobalTheory.LocM

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z B : Mdl Y i₀} {L : Lat B} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (hL : HasLatFlags Z L)

include hp hW hL

theorem HasLatFlags.isTr_tr (q q' : LatChart Z L) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) :
    q.IsTr q' e (q.tr q' e).val :=
  LatChart.isTr_tr (LatChart.existsUnique_isTr E H Dw Xo p W hp hW Y i₀ Z B L hL.1 q q' e).exists

theorem HasLatFlags.isLB (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) : (latLB Z L e).IsLB :=
  (LatGr.isLB_latLB_and_tr_add E H Dw Xo p W hp hW Y i₀ Z B L hL fun q q' e => ⟨_, hL.isTr_tr hp hW q q' e⟩).1 e

def HasLatFlags.latCls : (∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) →+ CechPic.Pic Z.X :=
  AddMonoidHom.mk' (fun e => cls _ (hL.isLB hp hW e)) fun e e' => by
    have h := CechPic.isLB_tens (hL.isLB hp hW e) (hL.isLB hp hW e')
    refine (CechPic.cls_eq_iff _ h).2 (CechPic.iso_of_chart h ⟨fun c => (c, c), fun _ _ h => ⟨h, h⟩, fun y c c' hc hc' => ?_⟩)
    refine .trans ?_ (CechPic.gm_tens (latLB Z L e) (latLB Z L e') (𝟙 _) y (c, c) (c', c') ⟨hc, hc⟩ ⟨hc', hc'⟩).symm
    exact (congrArg _ ((LatGr.isLB_latLB_and_tr_add E H Dw Xo p W hp hW Y i₀ Z B L hL
      fun q q' e => ⟨_, hL.isTr_tr hp hW q q' e⟩).2 c c' e e')).trans (map_mul _ _ _)

def HasLatFlags.degHom {k : Type} [Field k] (c : Curve k Z.X) : (∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) →+ ℤ :=
  c.degPic.comp (hL.latCls hp hW)

theorem HasLatFlags.degHom_apply {k : Type} [Field k] (c : Curve k Z.X) (e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ) :
    hL.degHom hp hW c e = c.degLat L e := rfl

omit hL in

theorem IsFlagCl.hasLatFlags {Z' : Mdl Y i₀} {L : Lat Z} (h : IsFlagCl Z (allSteps L) Z') (hty : ∀ σ, Z.ty σ = ∅) :
    HasLatFlags Z' L :=
  LatCover.hasLatFlags_of_allSteps E H Dw Xo p W hp hW Y i₀ Z' Z L
    (fun σ => by rw [h.2.1, hty, stepTy_allSteps, Finset.empty_union]) h.2.2.2.1

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p)

def crhTrue : CrHSt ct (flgTrue ct) := crhOf ct (IsHTLatOf (htmTrue ct)) (HTm.htFam ct)

namespace HTm

abbrev flagMdl (Z : ct.Mdl) : ct.Mdl := ct.flagCl Z (htFam ct Z).1

abbrev htLat (Z : ct.Mdl) : Lat Z := FlagFam.lat (htFam ct Z)

variable {ct} {Z : ct.Mdl} {n : ℕ}

theorem IsHTBlowup.ty_eq (H : IsHTBlowup ct Z (ct.Xn n)) (σ : D.host.E →+* ℂ) : Z.ty σ = ∅ := by
  obtain ⟨h, H'⟩ := (isHTBlowup_iff ct).1 H
  have e : Z.ty = (ct.Xn n).ty := by
    rw [H'.2.2]
    by_cases h' : ∃ Z', IsNBlow (ct.Xn n) (htIdl ct h) Z'
    · exact (blowUp_spec h').2.1
    · exact congrArg (·.ty) (dif_neg h' : blowUp (ct.Xn n) (htIdl ct h) = ct.Xn n)
  rw [e]
  exact ct.B.ty (some n) σ

theorem htFam_spec (h : ∃ L : Lat Z, IsHTLatOf (htmTrue ct) Z L) :
    IsHTLatOf (htmTrue ct) Z (htLat ct Z) ∧ (htFam ct Z).1 = allSteps (htLat ct Z) := by
  have e : htFam ct Z = FlagFam.full h.choose (.inr h.choose_spec) := dif_pos h
  rw [htLat, e, FlagFam.lat_full]
  exact ⟨h.choose_spec, rfl⟩

theorem hasLatFlags (h : ∃ L : Lat Z, IsHTLatOf (htmTrue ct) Z L) : HasLatFlags (flagMdl ct Z) (htLat ct Z) := by
  obtain ⟨n, H⟩ := (isHTLatOf_iff.1 h.choose_spec).1
  have h₁ : IsFlagCl Z (htFam ct Z).1 (flagMdl ct Z) := isFlagCl_flgTrue ct Z (htFam ct Z)
  exact IsFlagCl.hasLatFlags ct.hp ct.hW ((htFam_spec h).2 ▸ h₁) H.ty_eq

variable (ct Z) in

def wtLB (l : PsiT D → ℕ → ℤ) : LB (flagMdl ct Z).X := latLB (flagMdl ct Z) (htLat ct Z) (ct.expo l)

theorem degOf_wtLB {k : Type} [Field k] (c : Curve k (flagMdl ct Z).X) (l : PsiT D → ℕ → ℤ) :
    c.degOf (wtLB ct Z l) = c.degLat (htLat ct Z) (ct.expo l) := by rw [wtLB, Curve.degLat]

theorem degGr_eq (c : Curve ct.Fbar (flagMdl ct Z).X) (τ : PsiT D) (i : ℕ) :
    (crhTrue ct).degGr (Z := Z) c τ i = c.degLat (htLat ct Z) (-ct.expo (At.indWt τ i)) := rfl

end HTm

namespace At

theorem finrank_line_hyperplane (l : ct.Sum1) (τ : PsiT D) :
    Module.finrank ct.kbar (l.bar.submoduleOf (ct.eigBar τ)) = 1 ∧
      Module.finrank ct.kbar ((ct.psiBar.orthogonal l.bar).submoduleOf (ct.eigBar τ)) + 1 = N := by
  have k (P : Submodule ct.kbar ct.LaBar) :
      Module.finrank ct.kbar (P.submoduleOf (ct.eigBar τ)) = Module.finrank ct.kbar ↥(P ⊓ ct.eigBar τ) := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.submoduleOf, Submodule.map_comap_subtype, inf_comm]
  rw [k, k]
  refine And.imp_right (fun h => Eq.trans h (finrank_eigBar D A N j S κ p ct τ)) ?_
  obtain ⟨ε, hε0, hεe, hE⟩ := RedEig.exists_eigBar_eq_range D A N j S κ p ct τ
  obtain ⟨M', n₀, hc, hM, hM', hsp, hinj⟩ := LineSummand.sum1_bar_line D A N j S κ p ct l
  obtain ⟨hbb, hadj, hnd⟩ := RedForm.psiBar_props D A N j S κ p ct
  rw [hE]
  exact @EigenLine.line_hyperplane_cut ct.kbar _ (𝓞 D.host.E) _ ct.LaBar _ _ inferInstance
    (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La))
    (A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ct.psiBar (ct.ρ₀.comp (embV κ.c ct.W (embOf D τ))) ε l.bar M' n₀
    hbb hadj hnd hεe hε0 hc hM hM' hsp hinj

end At

example (Z : ct.Mdl) : Nonempty ((crhTrue ct).YsP Z) ∧ Nonempty ((crhTrue ct).CrvS Z) ∧ Nonempty (crhTrue ct).FlP ∧
    Nonempty (crhTrue ct).Sum1 :=
  ⟨ct.nonempty_spPt _, ct.nonempty_curve _, inferInstanceAs (Nonempty ct.FlP), nonempty_sum1 D A N j S κ p ct⟩

example : HasLatFlags ct.YY (Lat.top ct.Xm) :=
  IsFlagCl.hasLatFlags ct.hp ct.hW (ct.flagCl_allSteps ▸ isFlagCl_flgTrue ct ct.Xm (flgTrue ct).allFlags) (ct.B.ty none)

example : Nonempty (LatChart ct.YY (Lat.top ct.Xm)) :=
  have ⟨x⟩ := ct.nonempty_spPt ct.YY
  have ⟨q, _⟩ := (IsFlagCl.hasLatFlags ct.hp ct.hW
    (ct.flagCl_allSteps ▸ isFlagCl_flgTrue ct ct.Xm (flgTrue ct).allFlags) (ct.B.ty none)).2 (x.1 (Classical.arbitrary _))
  ⟨q⟩

example (Z : ct.Mdl) (h : ∃ L : Lat Z, IsHTLatOf (htmTrue ct) Z L) (c : Curve ct.Fbar (HTm.flagMdl ct Z).X) (τ : PsiT D)
    (i : ℕ) : c.degOf (HTm.wtLB ct Z (At.indWt τ i)) = -(crhTrue ct).degGr (Z := Z) c τ i := by
  rw [HTm.degOf_wtLB, HTm.degGr_eq, ← (HTm.hasLatFlags h).degHom_apply ct.hp ct.hW c,
    ← (HTm.hasLatFlags h).degHom_apply ct.hp ct.hW c, map_neg, neg_neg]

example (h : j = 0) (l : ct.Sum1) (F : ct.FlP) (τ : PsiT D) : F ∉ ct.locus l := fun hF => by
  have h₁ := Submodule.finrank_mono (show _ ≤ F.step τ j from (hF τ).1)
  have h₂ := h₁.trans_eq (finrank_step F τ j)
  rw [(ct.finrank_line_hyperplane l τ).1] at h₂
  omega

end GlobalTheory.LocM
end
end
