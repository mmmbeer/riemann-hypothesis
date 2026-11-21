import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDataOkOfTrueColumnChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumPosHerm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHypJetsAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ModelLamPDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointDecoratedLatticeAllTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
  GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.TrueColsTest

attribute [local instance] GlobalTheory.Mem.Col2.starE

section Normal

variable {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)

theorem exists_normal (q : S.D b) : ∃ g : S.G b, S.NormalFor b f (g • q) := by
  have h := Classical.epsilon_spec (p := fun r => ∃ g : S.G b, r = f (g • q)) ⟨f q, 1, by rw [one_smul]⟩
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ?_⟩
  unfold GStep.NormalFor
  rw [← hg]
  congr 1
  funext r
  apply propext
  constructor
  · rintro ⟨g', rfl⟩
    exact ⟨g' * g⁻¹, by rw [← mul_smul, inv_mul_cancel_right]⟩
  · rintro ⟨g', rfl⟩
    exact ⟨g' * g, by rw [mul_smul]⟩


end Normal

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem exists_pref (u : B.Word) (a : I.ι) (j : ℕ) (hj : j ≠ B.R.m) (b : (I.stp0 u a j).β) (q : (I.stp0 u a j).D b) :
    ∃ g : (I.stp0 u a j).G b, I.pref u a j b ((I.stp0 u a j).act b g q) := by
  have h2 := B.R.two_le_m
  by_cases h0 : j = 0
  · obtain ⟨g, hg⟩ := exists_normal (I.stp0 u a j) b (fun q' : (I.stp0 u a j).D b => q'.1.1.deco) q
    exact ⟨g, fun _ => hg, fun h => by omega, fun h => absurd h hj⟩
  · obtain ⟨g, hg⟩ := exists_normal (I.stp0 u a j) b (fun q' : (I.stp0 u a j).D b => cosetIn q') q
    exact ⟨g, fun h => absurd h h0, fun _ => hg, fun h => absurd h hj⟩



set_option maxHeartbeats 1600000 in

theorem laws (h : I.Ok) : I.Laws := by
  have hch := TC.ok_chains I h
  have hlev := LevelLaw.atIn_ok I h
  have hper := PerLaw.perIn_laws I h
  have hall := fun u a => laws_all (I.chIn u a) (I.atIn u a) B.fields.emb B.embLL (B.hcW u) (base_fOk B) (hch u a).1 (hlev u a)
    (I.perIn u a) (hper u a).1 B.places
  exact
    { pr := (base_fields_primes_ok B X).2.1
      ch := fun u a => (hch u a).1
      lev := hlev
      per := fun u a => (hper u a).1
      ovr := fun u a => (hper u a).2
      atL := fun u a => (hall u a).1
      fmL := fun u a => (hall u a).2
      xi0 := h.trueColumnChoices_heckeChar_reference_eq_one
      idx0 := fun a => (hch B.u₀ a).2.1
      bij0 := fun u a b => (ClsZero.stepZero_classes_bijective_same_deco I h u a b).1
      lat := fun u a => (hch u a).2.2 }

section Gen
variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem mem_formsK (S : GStep E K n) (hS : S.Free) (hF : (S.fam emb lam).Ok) (x : S.Cl → VV K lam) : x ∈ S.FormsK emb lam hF := by
  intro c g
  obtain rfl : g = 1 := Subtype.ext (hS c.1 g.1 _ g.2)
  rw [map_one]
  rfl

theorem forms_equiv (S S' : GStep E K n) (hS : S.Free) (hS' : S'.Free) (hF : (S.fam emb lam).Ok) (hF' : (S'.fam emb lam).Ok)
    (e0 : S.Cl ≃ S'.Cl) (hL : ∀ c, S'.Lsh _ (S'.rep (e0 c)) = S.Lsh _ (S.rep c)) :
    ∃ e : (S.hlat emb lam hF).V ≃ₗ[K] (S'.hlat emb lam hF').V,
      (∀ x, x ∈ (S.hlat emb lam hF).L ↔ e x ∈ (S'.hlat emb lam hF').L) ∧
        ∀ x, S'.embF emb σ lam hF' (e x) = fun c => S.embF emb σ lam hF x (e0.symm c) := by
  let e : S.FormsK emb lam hF ≃ₗ[K] S'.FormsK emb lam hF' :=
    { toFun := fun x => ⟨fun c => x.1 (e0.symm c), mem_formsK emb lam S' hS' hF' _⟩
      invFun := fun x => ⟨fun c => x.1 (e0 c), mem_formsK emb lam S hS hF _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun x => Subtype.ext (funext fun c => congrArg x.1 (e0.symm_apply_apply c))
      right_inv := fun x => Subtype.ext (funext fun c => congrArg x.1 (e0.apply_symm_apply c)) }
  refine ⟨e, fun x => ?_, fun x => rfl⟩
  show (∀ c, x.1 c ∈ delAtr emb lam (S.Lsh _ (S.rep c))) ↔ ∀ c, x.1 (e0.symm c) ∈ delAtr emb lam (S'.Lsh _ (S'.rep c))
  rw [← e0.forall_congr_right]
  refine forall_congr' fun c => ?_
  rw [e0.symm_apply_apply, hL]

theorem mt_finite {R : Ranks} {J : ChainIn E K ι R} (Q : PerIn J) (h : Q.Ok) (hH : ∀ b, Q.H b = ⊤) :
    FiniteDimensional ℂ (Q.Mt emb σ) := by
  letI := Q.clFin h
  haveI : FiniteDimensional ℂ (VV ℂ Q.sgT) := Module.Finite.of_basis (bVV ℂ Q.sgT)
  let r : Q.Mt emb σ →ₗ[ℂ] (Q.S'.Cl → VV ℂ Q.sgT) :=
    { toFun := fun F c => ⟨F.1 c.1 (Q.S'.rep c), (F.2 c.1 _).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective r ((injective_iff_map_eq_zero r).2 fun F hF => ?_)
  apply Subtype.ext
  funext b d
  have h0 : F.1 b (Q.S'.rep (Q.S'.cl b d)) = 0 := congrArg Subtype.val (congrFun hF (Q.S'.cl b d))
  have h1 := (F.2 b (Q.S'.rep (Q.S'.cl b d))).2 (Q.S'.mv b d) (by rw [hH]; trivial)
  rw [h0, map_zero, smul_zero] at h1
  exact (congrArg (F.1 b) (Q.S'.mv_smul b d)).symm.trans h1
end Gen

set_option maxHeartbeats 1600000 in

theorem law0 (h : I.Ok) (l : I.Laws) : I.Law0 l := by
  intro u a
  obtain ⟨e, h1, h2⟩ := forms_equiv B.fields.emb B.embLL (lamT (B.hcW u) 0) (I.stp u I.mu0 0) (I.stp u a 0)
    (l.lev u _).free0 (l.lev u a).free0
    ((l.fmL u I.mu0).fam 0) ((l.fmL u a).fam 0) (I.eCls0 l u a)
    fun c => congrArg (fun d : DecoSet B.fields.E (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs => d.1.Lsh)
      ((ClsZero.stepZero_classes_bijective_same_deco I h u a _).2 c)
  exact ⟨e, h1, h2⟩

theorem ipC_herm (l : I.Laws) (u : B.Word) (x y) :
    starRingEnd ℂ (((I.cols l).fm u).ipC 0 y x) = ((I.cols l).fm u).ipC 0 x y := by
  unfold MemberForms.ipC
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul]
  congr 1
  · simp [ColumnChain.wt]
  · exact (ClassSumPos.ipVal_herm _ _ _ _ _).symm

theorem ipC_pos (l : I.Laws) (u : B.Word) (x) (hx : x ∈ ((I.cols l).mem u).A.Mu0) (h0 : x ≠ 0) :
    0 < (((I.cols l).fm u).ipC 0 x x).re := by
  letI := (I.chIn u I.mu0).clFin (l.ch u _) 0
  exact (ClassSumPos.classSum_pos_herm (I.stp u I.mu0 0) B.fields.emb B.embLL (lamT (B.hcW u) 0) (base_fOk B) ((l.ch u _).step 0)).1 x hx h0

theorem fits (l : I.Laws) : RowsRestModel.Fits (I.cols l)
    fun a => Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL) := by
  have key : ∀ u a, Nonempty (((I.cols l).PTw u a).Mt ≃ₗ[ℂ]
      RowsRestModel.Eu (Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL))) := fun u a => by
    haveI := mt_finite B.fields.emb B.embLL (I.perIn B.u₀ a) (l.per _ a) fun _ => rfl
    have key : Nonempty ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL ≃ₗ[ℂ]
        RowsRestModel.Eu (Module.finrank ℂ ((I.perIn B.u₀ a).Mt B.fields.emb B.embLL))) :=
      FiniteDimensional.nonempty_linearEquiv_of_finrank_eq finrank_euclideanSpace_fin.symm
    exact key
  refine ⟨fun u => key u I.mu0, key, fun u x y => ipC_herm l u _ _, fun u x => ?_, fun u x hx => ?_⟩
  · by_cases h0 : x.1 = 0
    · simp [h0, MemberForms.ipC]
    · exact (ipC_pos l u x.1 x.2.1 h0).le
  · by_contra h0
    have := ipC_pos l u x.1 x.2.1 fun e => h0 (Subtype.ext e)
    rw [hx] at this
    simp at this

theorem later (l : I.Laws) (hB : StagesInhab.HasLetters B.toPre) : Nonempty (TC.Later B (I.cols l)) := by
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hB
  let W := RowsRestModel.model (fits l) 1 1 1
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => ipC_herm l u x y) (fun u x hx h => ipC_pos l u x hx h) (show 1 ≤ 2 * 1 by omega)
  obtain ⟨G⟩ := GJInhab.nonempty_stage B (I.cols l)
  exact ⟨⟨GaloisStage.adapt W, V, S, N, G⟩⟩

theorem kStd_spec (X : PreX B.toPre) (u : B.Word) (n : ℕ) :
    (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf (kStd X u n) p ∧ p.deco.1.N = stdLat B.fields.E n) ∧
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) (kStd X u n) = 1) ∧
    ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 (((kStd X u n)⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) :=
  Classical.epsilon_spec (BasePoint.exists_kStd X (base_fields_primes_ok B X).2.1 u n)

theorem exists_pre : ∃ (P : Pre) (X : PreX P) (f : Top.Fr P), StagesInhab.HasLetters P ∧ InEx.Oriented X f.P ∧
    (letI := P.host.cmStar; DiagSpaces P.sp) ∧ (∀ u, (P.duStar u : ℝ) = duStarOf P.host (P.hcW u)) ∧
    (letI := P.host.cmStar; ∀ (a : Fin P.sp.X'.rank) (b : Fin (P.sp.X P.R.m).rank), (a : ℕ) = b →
      P.sp.iX' (P.sp.X'.frame a) = (P.sp.X P.R.m).frame b) ∧
    ∀ u, P.cOf u * (X.piT u : P.host.E) = (X.piT P.u₀ : P.host.E) := by
  obtain ⟨P, hL, ⟨X₀⟩, -, hdu⟩ := KerT.JetsInhab.exists_pre_sized
  obtain ⟨f⟩ : Nonempty (Top.Fr P) := P.nonempty_hframe X₀.e_even
  obtain ⟨X, hX⟩ := InEx.exists_oriented X₀ f.P
  letI := P.host.cmStar
  have hs : ∀ x : P.host.E, star x = P.host.conj x := bridge_star_holds P.R P.host
  have hpz : star (X.piT P.u₀ : P.host.E) * (X.piT P.u₀ : P.host.E) = (P.T P.u₀ : P.host.E) := by
    rw [hs, mul_comm]
    exact X.piT_norm P.u₀
  have hne : ∀ u, (X.piT u : P.host.E) ≠ 0 := fun u h => by
    have h1 := X.piT_norm u
    rw [h, zero_mul] at h1
    exact (P.T_prime u).ne_zero (by exact_mod_cast h1.symm)
  let cm := host_cmData P.R P.host
  have hT := P.T_prime P.u₀
  let Q : Pre := { P with
    sp := DiagSp.spacesNorm P.R cm _ hT _ hpz
    Y_sigval := fun j _ τ => DiagSp.spacesNorm_Y_sig P.R cm _ hT _ hpz j τ
    auxiliaryFrame := fun j _ hj => DiagSp.spacesNorm_hasFrame P.R cm _ hT _ hpz j hj
    V_pos := fun j _ _ => rfl
    z_norm := DiagSp.spacesNorm_z_norm P.R cm _ hT _ hpz
    sp_T := rfl
    cOf := fun u => (X.piT P.u₀ : P.host.E) / (X.piT u : P.host.E)
    cOf_ne := fun u => div_ne_zero (hne _) (hne _)
    cOf_eq := fun u => by
      have h1 := hne u
      have h2 : P.host.conj (X.piT u : P.host.E) ≠ 0 := (map_ne_zero _).2 h1
      rw [← X.piT_norm u, ← X.piT_norm P.u₀, map_div₀]
      field_simp }
  refine ⟨Q, { X with }, f, hL, hX, DiagSp.spacesNorm_coord P.R cm _ hT _ hpz, hdu, fun a b hab => ?_,
    fun u => div_mul_cancel₀ _ (hne u)⟩
  have gen : ∀ (n N : ℕ) (a : Fin n) (b : Fin N), (a : ℕ) = b →
      GlobalTheory.Mem.DiagSp.extTo n N (Pi.basisFun P.host.E (Fin n) a) = Pi.basisFun P.host.E (Fin N) b := by
    intro n N a b hab
    funext i
    simp only [GlobalTheory.Mem.DiagSp.extTo, Pi.basisFun_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  exact gen _ _ a b hab



end GlobalTheory.Mem.Col2.TrueColsTest

end
