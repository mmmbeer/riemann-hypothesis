import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding
import Development.AutomorphicSpectrum.Proofs.HermitianForms.OneAddHsInvPowLintegralLtTop
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AlmostIsomOfGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriKeeps
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditive
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosedStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspace
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVectorStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditiveStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.WordBoundOfDelta
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticOnUJOfWordBound
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticVectorExponentialSeries

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def IsIrrK (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ IsKStable G π S ∧
    ∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S

def isoGens (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Set (Submodule ℂ H) :=
  {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k ∈ maxCpt G, ∀ w ∈ S, T (π k w) = π k (T w)}

theorem orthogonal_kstable (hG : IsLinRed G) (hA : IsAdmOn G π) {S : Submodule ℂ H}
    (hS : IsKStable G π S) : IsKStable G π Sᗮ := by
  intro k hk y hy
  rw [Submodule.mem_orthogonal]
  intro s hs
  have hk' : star k ∈ maxCpt G := ⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩
  have h1 : π k (π (star k) s) = s := by
    have hm : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    rw [← ContinuousLinearMap.comp_apply, ← hA.1.2 k hk.1 (star k) hk'.1, hm, hA.1.1]
    rfl
  let Lk : H →ₗᵢ[ℂ] H := ⟨(π k : H →ₗ[ℂ] H), hA.2.2.1 k hk⟩
  have h2 : inner ℂ (π k (π (star k) s)) (π k y) = inner ℂ (π (star k) s) y := Lk.inner_map_map _ _
  rw [← h1, h2]
  exact Submodule.inner_right_of_mem_orthogonal (hS _ hk' s hs) hy

theorem sSup_kstable {A : Set (Submodule ℂ H)} (hA : ∀ S ∈ A, IsKStable G π S) :
    IsKStable G π (sSup A) := by
  intro k hk w hw
  have h : sSup A ≤ (sSup A).comap (π k : H →ₗ[ℂ] H) :=
    sSup_le fun S hS x hx => Submodule.mem_comap.2 (le_sSup hS (hA S hS k hk x hx))
  exact h hw

theorem exists_irr_family (hG : IsLinRed G) (hA : IsAdmOn G π) (m : ℕ) :
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Module.finrank ℂ S = m → IsKStable G π S →
      ∃ F : Set (Submodule ℂ H), F.Finite ∧ (∀ I ∈ F, IsIrrK G π I) ∧ S ≤ sSup F := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hfin hm hS
    by_cases hirr : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S
    · refine ⟨{S}, Set.finite_singleton S, ?_, ?_⟩
      · rintro I rfl
        exact ⟨hfin, hS, hirr⟩
      · simp
    · push_neg at hirr
      obtain ⟨S', hle, hS', hne0, hneS⟩ := hirr
      haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
      have hlt : S' < S := lt_of_le_of_ne hle hneS
      have hT : IsKStable G π (S ⊓ S'ᗮ) := fun k hk v hv =>
        ⟨hS k hk v hv.1, orthogonal_kstable hG hA hS' k hk v hv.2⟩
      haveI : FiniteDimensional ℂ (S ⊓ S'ᗮ : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_left
      have hltT : S ⊓ S'ᗮ < S := by
        refine lt_of_le_of_ne inf_le_left fun h => hne0 ?_
        have hSo : S ≤ S'ᗮ := inf_eq_left.1 h
        rw [eq_bot_iff]
        intro x hx
        have h0 : ⟪x, x⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hx (hSo (hle hx))
        exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 h0)
      have hd₁ : Module.finrank ℂ S' < m := hm ▸ Submodule.finrank_lt_finrank_of_lt hlt
      have hd₂ : Module.finrank ℂ (S ⊓ S'ᗮ : Submodule ℂ H) < m :=
        hm ▸ Submodule.finrank_lt_finrank_of_lt hltT
      obtain ⟨F₁, hF₁, hI₁, hle₁⟩ := ih _ hd₁ S' inferInstance rfl hS'
      obtain ⟨F₂, hF₂, hI₂, hle₂⟩ := ih _ hd₂ (S ⊓ S'ᗮ) inferInstance rfl hT
      refine ⟨F₁ ∪ F₂, hF₁.union hF₂, ?_, ?_⟩
      · rintro I (hI | hI)
        · exact hI₁ I hI
        · exact hI₂ I hI
      · intro v hv
        have hp : ((S'.orthogonalProjection v : S') : H) ∈ S' := (S'.orthogonalProjection v).2
        have hq : v - (S'.orthogonalProjection v : H) ∈ S ⊓ S'ᗮ :=
          ⟨S.sub_mem hv (hle hp), Submodule.sub_starProjection_mem_orthogonal (K := S') v⟩
        have e : v = (S'.orthogonalProjection v : H) + (v - (S'.orthogonalProjection v : H)) := by abel
        rw [e, sSup_union]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (hle₁ hp)) (Submodule.mem_sup_right (hle₂ hq))

theorem isoGens_kstable {S S' : Submodule ℂ H} (hS : IsKStable G π S) (h : S' ∈ isoGens G π S) :
    IsKStable G π S' := by
  obtain ⟨T, rfl, hT⟩ := h
  rintro k hk _ ⟨s, hs, rfl⟩
  exact ⟨π k s, hS k hk s hs, hT k hk s hs⟩

theorem le_sSup_isoGens (S : Submodule ℂ H) : S ≤ sSup (isoGens G π S) := by
  refine le_trans (le_of_eq ?_) (le_sSup (show S.map LinearMap.id ∈ isoGens G π S from
    ⟨LinearMap.id, rfl, fun k _ w _ => rfl⟩))
  simp

theorem map_mem_of_gen {Y S S' : Submodule ℂ H} (hSY : sSup (isoGens G π S) ≤ Y) (h : S' ∈ isoGens G π S)
    (D : Y →ₗ[ℂ] H) (hD : ∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y))
    (hS : IsKStable G π S) {x : H} (hx : x ∈ S') (hxY : x ∈ Y) : D ⟨x, hxY⟩ ∈ Y := by
  obtain ⟨T, rfl, hT⟩ := h
  obtain ⟨s, hs, rfl⟩ := hx
  have hTY : ∀ w ∈ S, T w ∈ Y := fun w hw =>
    hSY (le_sSup (show S.map T ∈ isoGens G π S from ⟨T, rfl, hT⟩) ⟨w, hw, rfl⟩)
  let f : S →ₗ[ℂ] H := D ∘ₗ (T.domRestrict S).codRestrict Y (fun w => hTY w w.2)
  obtain ⟨T', hT'⟩ := LinearMap.exists_extend f
  have hval : ∀ w (hw : w ∈ S), T' w = D ⟨T w, hTY w hw⟩ := fun w hw =>
    LinearMap.congr_fun hT' ⟨w, hw⟩
  have hcomm : ∀ k ∈ maxCpt G, ∀ w ∈ S, T' (π k w) = π k (T' w) := by
    intro k hk w hw
    rw [hval _ (hS k hk w hw), hval w hw]
    exact hD k hk _ _ (hT k hk w hw)
  have hmem : S.map T' ∈ isoGens G π S := ⟨T', rfl, hcomm⟩
  have : T' s ∈ Y := hSY (le_sSup hmem ⟨s, hs, rfl⟩)
  rwa [hval s hs] at this

theorem exists_isotypic_sum : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hA : IsAdmOn G π) {v : H} (hv : IsKFinOn G π v), ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ IsKStable G π Y ∧ ∀ D : Y →ₗ[ℂ] H, (∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y)) → ∀ y, D y ∈ Y := by
  intro n G H _ _ _ π hG hA v hv
  obtain ⟨S, hfin, hvS, hS⟩ := hv
  obtain ⟨F, hF, hI, hle⟩ := exists_irr_family hG hA _ S hfin rfl hS
  let iso : Submodule ℂ H → Submodule ℂ H := fun I => sSup (isoGens G π I)
  have hisoK : ∀ I ∈ F, IsKStable G π (iso I) := fun I hIF =>
    sSup_kstable fun S' h => isoGens_kstable (hI I hIF).2.1 h
  have hisoF : ∀ I ∈ F, FiniteDimensional ℂ (iso I) := fun I hIF =>
    hA.2.2.2 I (hI I hIF).1 (hI I hIF).2.1 (hI I hIF).2.2
  have hYle : ∀ I ∈ F, iso I ≤ sSup (iso '' F) := fun I hIF => le_sSup ⟨I, hIF, rfl⟩
  refine ⟨sSup (iso '' F), ?_, ?_, ?_, ?_⟩
  · rw [sSup_eq_iSup']
    haveI : Finite ↥(iso '' F) := (hF.image iso).to_subtype
    haveI : ∀ a : ↥(iso '' F), FiniteDimensional ℂ (a : Submodule ℂ H) := by
      rintro ⟨_, I, hIF, rfl⟩
      exact hisoF I hIF
    exact Submodule.finiteDimensional_iSup _
  · exact (sSup_le fun I hIF => (le_sSup_isoGens I).trans (hYle I hIF)) (hle hvS)
  · refine sSup_kstable ?_
    rintro _ ⟨I, hIF, rfl⟩
    exact hisoK I hIF
  · intro D hD y
    have hP : sSup (iso '' F) ≤ ((sSup (iso '' F)).comap D).map (sSup (iso '' F)).subtype := by
      refine sSup_le ?_
      rintro _ ⟨I, hIF, rfl⟩
      refine sSup_le fun S' hS' x hx => ?_
      have hxY : x ∈ sSup (iso '' F) := hYle I hIF (le_sSup hS' hx)
      exact ⟨⟨x, hxY⟩, map_mem_of_gen (hYle I hIF) hS' D hD (hI I hIF).2.1 hx hxY, rfl⟩
    obtain ⟨y', hy', he⟩ := hP y.2
    have hyy : y' = y := Subtype.ext he
    subst hyy
    exact hy'

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic

end
end

section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
open MeasureTheory Topology Set Filter CompanionTheory.D.gk.admitted.Gard

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Gard

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Op

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (μ : Measure Γ) [μ.IsHaarMeasure]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_avg_op (ρ : Γ → H →L[ℂ] H) (hρ : ∀ u, Continuous fun x => ρ x u) {w : Γ → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) :
    ∃ T : H →L[ℂ] H, ∀ u, T u = ∫ x, w x • ρ x u ∂μ := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ i : tsupport w, ‖ρ i‖ ≤ C := by
    refine banach_steinhaus (g := fun i : tsupport w => ρ i) fun u => ?_
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn (s := tsupport w) hc (hρ u).continuousOn
    exact ⟨C, fun i => hC i i.2⟩
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ x, w x • ρ x u ∂μ
      map_add' := fun u v => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_w μ ρ hρ hw hc u) (integrable_w μ ρ hρ hw hc v)
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        simp only [smul_comm c] }
  have hwi : Integrable (fun x => ‖w x‖) μ := (hw.integrable_of_hasCompactSupport hc).norm
  refine ⟨L.mkContinuous ((∫ x, ‖w x‖ ∂μ) * C) fun u => ?_, fun u => rfl⟩
  have hb : ‖∫ x, w x • ρ x u ∂μ‖ ≤ ∫ x, ‖w x‖ * (C * ‖u‖) ∂μ := by
    refine norm_integral_le_of_norm_le (hwi.mul_const _) (Eventually.of_forall fun x => ?_)
    rw [norm_smul]
    by_cases hx : w x = 0
    · simp [hx]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact ((ρ x).le_opNorm u).trans (mul_le_mul_of_nonneg_right
        (hC ⟨x, subset_tsupport _ hx⟩) (norm_nonneg _))
  rw [integral_mul_const] at hb
  rw [mul_assoc]
  exact hb

end Op

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}

def GT (_ : IsLinRed G) (_ : IsClosed G) : Type := {g : Matrix (Fin n) (Fin n) ℂ // g ∈ G}

variable {hG : IsLinRed G} {hcl : IsClosed G}

def toM (x : GT hG hcl) : Matrix (Fin n) (Fin n) ℂ := x.1

theorem det_unit (x : GT hG hcl) : IsUnit (toM x).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (hG.isUnit _ x.2)

instance : Mul (GT hG hcl) := ⟨fun x y => ⟨x.1 * y.1, hG.mul_mem _ x.2 _ y.2⟩⟩

instance : One (GT hG hcl) := ⟨⟨1, hG.one_mem⟩⟩

instance : Inv (GT hG hcl) := ⟨fun x => ⟨x.1⁻¹, hG.inv_mem _ x.2⟩⟩

instance : Group (GT hG hcl) :=
  Group.ofLeftAxioms (fun x y z => Subtype.ext (Matrix.mul_assoc x.1 y.1 z.1))
    (fun x => Subtype.ext (Matrix.one_mul x.1))
    (fun x => Subtype.ext (Matrix.nonsing_inv_mul x.1 (det_unit x)))

theorem toM_mul (x y : GT hG hcl) : toM (x * y) = toM x * toM y := rfl

theorem toM_one : toM (1 : GT hG hcl) = 1 := rfl

instance : TopologicalSpace (GT hG hcl) := inferInstanceAs (TopologicalSpace {g // g ∈ G})

instance : T2Space (GT hG hcl) := inferInstanceAs (T2Space {g // g ∈ G})

instance : SecondCountableTopology (GT hG hcl) :=
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  inferInstanceAs (SecondCountableTopology {g // g ∈ G})

theorem emb_toM : IsClosedEmbedding (toM : GT hG hcl → Matrix (Fin n) (Fin n) ℂ) :=
  hcl.isClosedEmbedding_subtypeVal

instance : LocallyCompactSpace (GT hG hcl) :=
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  emb_toM.locallyCompactSpace

instance : IsTopologicalGroup (GT hG hcl) where
  continuous_mul := by
    rw [emb_toM.isInducing.continuous_iff]
    exact (emb_toM.continuous.comp continuous_fst).mul (emb_toM.continuous.comp continuous_snd)
  continuous_inv := by
    rw [emb_toM.isInducing.continuous_iff]
    refine continuous_iff_continuousAt.2 fun x => ?_
    have h1 : ContinuousAt (Inv.inv : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (toM x) := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (det_unit x).ne_zero
    exact h1.comp emb_toM.continuous.continuousAt

instance : MeasurableSpace (GT hG hcl) := borel _

instance : BorelSpace (GT hG hcl) := ⟨rfl⟩

theorem exists_toM {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) : ∃ x : GT hG hcl, toM x = g := ⟨⟨g, hg⟩, rfl⟩

theorem supp_local {f : Matrix (Fin n) (Fin n) ℂ → ℝ} {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) (g₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U ∈ 𝓝 g₀, ∃ C : Set (GT hG hcl), IsCompact C ∧ ∀ g ∈ U, ∀ x ∉ C, f (toM x⁻¹ * g) = 0 := by
  refine ⟨Metric.closedBall g₀ 1, Metric.closedBall_mem_nhds _ one_pos, _,
    emb_toM.isCompact_preimage (isCompact_mul_inv (isCompact_closedBall g₀ 1) hS hd), fun g hg x hx => ?_⟩
  by_contra h
  have hB := hfS _ h
  refine hx ⟨(g, toM x⁻¹ * g), ⟨hg, hB⟩, ?_⟩
  have hu : IsUnit (toM x⁻¹ * g).det := isUnit_iff_ne_zero.2 (hd _ hB)
  have e : g = toM x * (toM x⁻¹ * g) := by
    rw [← Matrix.mul_assoc, ← toM_mul, mul_inv_cancel, toM_one, Matrix.one_mul]
  show g * (toM x⁻¹ * g)⁻¹ = toM x
  calc g * (toM x⁻¹ * g)⁻¹ = toM x * (toM x⁻¹ * g) * (toM x⁻¹ * g)⁻¹ := by rw [← e]
    _ = toM x := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem contDiff_avg {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (μ : Measure (GT hG hcl)) [IsFiniteMeasureOnCompacts μ]
    (v : GT hG hcl → H) (hv : Continuous v) {f : Matrix (Fin n) (Fin n) ℂ → ℝ}
    {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiff ℝ ∞ f) (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) :
    ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => ∫ x : GT hG hcl, f (toM x⁻¹ * g) • v x ∂μ := by
  have hq : Continuous fun x : GT hG hcl => (toM x⁻¹, v x) :=
    (emb_toM.continuous.comp continuous_inv).prodMk hv
  have key := contDiff_integral_comp μ _ (contDiff_Phi (H := H) hf) _ hq fun g₀ => by
    obtain ⟨U, hU, C, hC, h⟩ := supp_local (hG := hG) (hcl := hcl) hS hd hfS g₀
    refine ⟨U, hU, C, hC, fun g hg x hx => ?_⟩
    simp only [h g hg x hx, zero_smul]
  simpa only using key

theorem toM_inv_of_unitary {k : GT hG hcl} (hk : toM k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    toM k⁻¹ = (toM k)ᴴ :=
  Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.1 hk)

theorem smooth_of_commutant_stable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hcl : IsClosed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G)
    (hK : ∀ k ∈ maxCpt G, ∀ v, ‖π k v‖ = ‖v‖) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y]
    (hY : ∀ T : H →L[ℂ] H, (∀ k ∈ maxCpt G, ∀ u, T (π k u) = π k (T u)) → ∀ y ∈ Y, T y ∈ Y) :
    ∀ v ∈ Y, IsSmoothVec G π v := by
  intro v hv
  let μ : Measure (GT hG hcl) := Measure.haar
  obtain ⟨h1, hm⟩ := hrep
  let ρ : GT hG hcl → H →L[ℂ] H := fun x => π (toM x)
  have hρ : ∀ u, Continuous fun x => ρ x u := fun u =>
    (hc u).comp_continuous emb_toM.continuous fun x => x.2
  have hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u) := fun x y u => by
    show π (toM x * toM y) u = π (toM x) (π (toM y) u)
    rw [hm (toM x) x.2 (toM y) y.2, ContinuousLinearMap.comp_apply]
  have hρ1 : ∀ u, ρ 1 u = u := fun u => by simp only [ρ, toM_one, h1, ContinuousLinearMap.one_apply]
  obtain ⟨V, hV, hclose⟩ := exists_nhds_close ρ hρ hρ1 Y
  have hVi : V⁻¹ ∈ 𝓝 (1 : GT hG hcl) := inv_mem_nhds_one _ hV
  rw [emb_toM.isInducing.nhds_eq_comap, mem_comap] at hVi
  obtain ⟨W, hW, hWV⟩ := hVi
  have hD : {y : Matrix (Fin n) (Fin n) ℂ | y.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ) :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  obtain ⟨f, S, hf, hf0, hf1, hS, hSW, hfS, hfk⟩ := exists_bump (inter_mem hW hD)
  let w : GT hG hcl → ℝ := fun x => f (toM x⁻¹)
  have hw : Continuous w := hf.continuous.comp (emb_toM.continuous.comp continuous_inv)
  have hcw : HasCompactSupport w := by
    refine HasCompactSupport.intro (emb_toM.isCompact_preimage hS).inv fun x hx => ?_
    by_contra h
    exact hx (hfS _ h)
  have h0 : 0 ≤ w := fun x => hf0 _
  have hw1 : w 1 ≠ 0 := by simpa only [w, inv_one, toM_one] using hf1
  obtain ⟨T, hT⟩ := exists_avg_op μ ρ hρ hw hcw
  have hTK : ∀ k ∈ maxCpt G, ∀ u, T (π k u) = π k (T u) := by
    intro k hk u
    obtain ⟨k', rfl⟩ := exists_toM (hG := hG) (hcl := hcl) hk.1
    rw [hT, hT]
    refine T_comm μ ρ hρ hmul hw hcw h0 hw1 k' (fun x => ?_) u
    simp only [w, _root_.mul_inv_rev, inv_inv]
    rw [← mul_assoc, toM_mul, toM_mul, toM_inv_of_unitary hk.2, hfk _ hk.2]
  have hinj : ∀ y ∈ Y, T y = 0 → y = 0 := by
    intro y hy hTy
    rw [hT] at hTy
    refine eq_zero_of_alt_alt μ ρ hρ hw hcw h0 hw1 y (fun x hx => hclose x ?_ y hy) hTy
    have : x⁻¹ ∈ V⁻¹ := hWV (hSW (hfS _ hx)).1
    simpa using this
  obtain ⟨u, rfl⟩ := exists_preimage Y T (hY T hTK) hinj v hv
  have hF := contDiff_avg μ (fun x => ρ x u) (hρ u) hf hS (fun B hB => (hSW hB).2) hfS
  refine ⟨fun z => ∫ x : GT hG hcl, f (toM x⁻¹ * Matrix.of z) • ρ x u ∂μ, hF, fun z hz => ?_⟩
  obtain ⟨g', hg'⟩ := exists_toM (hG := hG) (hcl := hcl) hz
  show π (Matrix.of z) (T u) = ∫ x : GT hG hcl, f (toM x⁻¹ * Matrix.of z) • ρ x u ∂μ
  rw [← hg']
  show ρ g' (T u) = _
  rw [hT, apply_alt μ ρ hρ hmul hw hcw]
  simp only [w, _root_.mul_inv_rev, inv_inv, toM_mul]

section ClosedNeeded

def gl1 : Set (Matrix (Fin 1) (Fin 1) ℂ) := {g | g 0 0 ≠ 0}

end ClosedNeeded

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Gard

end
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.PolyGrowth

variable {n : ℕ} {ε : Fin n → Bool}

theorem wt_eq_sum (g : Matrix (Fin n) (Fin n) ℂ) : wt g = ∑ i, ∑ j, ‖g i j‖ ^ 2 := by
  unfold wt
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem entry_sq_le_wt (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ^ 2 ≤ wt g := by
  rw [wt_eq_sum]
  calc ‖g i j‖ ^ 2 ≤ ∑ j, ‖g i j‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem one_le_wt {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (a : Fin n) : 1 ≤ wt g := by
  have h := congrFun (congrFun hg a) a
  have hd : ∀ i, ‖(if ε i = true then (1 : ℂ) else -1)‖ = 1 := fun i => by split_ifs <;> simp
  have h1 : ‖Jm ε a a‖ = 1 := by
    rw [Jm, Matrix.diagonal_apply_eq]; exact hd a
  have e : (gᴴ * Jm ε * g) a a = ∑ i, star (g i a) * (if ε i = true then (1 : ℂ) else -1) * g i a := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Jm, Matrix.mul_diagonal, conjTranspose_apply]
  rw [← h1, ← h, e, wt_eq_sum]
  calc ‖∑ i, star (g i a) * (if ε i = true then (1 : ℂ) else -1) * g i a‖
      ≤ ∑ i, ‖star (g i a) * (if ε i = true then (1 : ℂ) else -1) * g i a‖ := norm_sum_le _ _
    _ = ∑ i, ‖g i a‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_mul, hd i, norm_star, mul_one, sq]
    _ ≤ ∑ i, ∑ j, ‖g i j‖ ^ 2 := Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a)

theorem inUJ_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUJ ε a) (hb : inUJ ε b) : inUJ ε (a * b) := by
  unfold inUJ at *
  calc (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [ha, hb]

theorem isUnit_of_inUJ' {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : IsUnit g := by
  have h : Jm ε * gᴴ * Jm ε * g = 1 := by
    calc Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Jm_mul_self]
  exact ⟨⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.mp h, h⟩, rfl⟩

theorem isCompact_wt_le (ε : Fin n → Bool) (R : ℝ) :
    IsCompact {h : Matrix (Fin n) (Fin n) ℂ | inUJ ε h ∧ wt h ≤ R} := by
  have hwt : Continuous (wt : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
    have : (wt : Matrix (Fin n) (Fin n) ℂ → ℝ) = fun g => ∑ i, ∑ j, ‖g i j‖ ^ 2 := funext wt_eq_sum
    rw [this]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((continuous_id.matrix_elem i j).norm).pow 2
  have hcl : IsClosed {h : Matrix (Fin n) (Fin n) ℂ | inUJ ε h ∧ wt h ≤ R} := by
    refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_le hwt continuous_const)
    exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      Metric.closedBall (0 : ℂ) (R + 1)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 _
  refine IsCompact.of_isClosed_subset hK hcl ?_
  rintro h ⟨-, hR⟩ i - j -
  have h1 := (entry_sq_le_wt h i j).trans hR
  rw [mem_closedBall_zero_iff]
  nlinarith [sq_nonneg (‖h i j‖ - 1), norm_nonneg (h i j)]

section rep

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_bound_on_compact [CompleteSpace H] (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε))
    {S : Set (Matrix (Fin n) (Fin n) ℂ)} (hS : IsCompact S) (hSU : S ⊆ UJset ε) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ h ∈ S, ‖π h‖ ≤ B := by
  have hb : ∀ x : H, ∃ C, ∀ i : S, ‖π (i : Matrix (Fin n) (Fin n) ℂ) x‖ ≤ C := fun x => by
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn ((hc x).mono hSU)
    exact ⟨C, fun i => hC i i.2⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus (g := fun i : S => π (i : Matrix (Fin n) (Fin n) ℂ)) hb
  exact ⟨max C' 1, le_max_right _ _, fun h hh => (hC' ⟨h, hh⟩).trans (le_max_left _ _)⟩

theorem pow_bound (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) {h : Matrix (Fin n) (Fin n) ℂ} (hh : inUJ ε h)
    {B : ℝ} (hB : 0 ≤ B) (hb : ‖π h‖ ≤ B) (m : ℕ) :
    inUJ ε (h ^ m) ∧ ∀ x, ‖π (h ^ m) x‖ ≤ B ^ m * ‖x‖ := by
  induction m with
  | zero =>
    refine ⟨?_, fun x => ?_⟩
    · simp [inUJ]
    · simp [hrep.1]
  | succ m ih =>
    refine ⟨by rw [pow_succ]; exact inUJ_mul ih.1 hh, fun x => ?_⟩
    rw [pow_succ, hrep.2 _ ih.1 _ hh, ContinuousLinearMap.comp_apply]
    calc ‖π (h ^ m) (π h x)‖ ≤ B ^ m * ‖π h x‖ := ih.2 _
      _ ≤ B ^ m * (B * ‖x‖) := by
          gcongr
          exact ((π h).le_opNorm x).trans (by gcongr)
      _ = B ^ (m + 1) * ‖x‖ := by ring

end rep

theorem trace_exp_smul {L : Matrix (Fin n) (Fin n) ℂ} (hL : L.IsHermitian) (t : ℝ) :
    (NormedSpace.exp (t • L)).trace.re = ∑ i, Real.exp (t * hL.eigenvalues i) := by
  set V : Matrix (Fin n) (Fin n) ℂ := (hL.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hV
  have h1 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.1 hL.eigenvectorUnitary.2
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hL.eigenvectorUnitary.2
  have hsp : L = V * diagonal (fun i => (hL.eigenvalues i : ℂ)) * Vᴴ := by
    have h0 := hL.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h0
    conv_lhs => rw [h0]
    simp only [Matrix.star_eq_conjTranspose]
    rfl
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨V, Vᴴ, h2, h1⟩
  have hd : diagonal (fun i => ((t * hL.eigenvalues i : ℝ) : ℂ)) =
      t • diagonal (fun i => (hL.eigenvalues i : ℂ)) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp
  have hs : t • L = (U : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun i => ((t * hL.eigenvalues i : ℝ) : ℂ)) *
      ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
    show t • L = V * _ * Vᴴ
    rw [hd, Matrix.mul_smul, Matrix.smul_mul, ← hsp]
  rw [hs, Matrix.exp_units_conj, Matrix.trace_units_conj, Matrix.exp_diagonal, trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.exp_def, ← Complex.exp_eq_exp_ℂ, Complex.exp_ofReal_re]

theorem exp_smul_add (L : Matrix (Fin n) (Fin n) ℂ) (s r : ℝ) :
    NormedSpace.exp (s • L) * NormedSpace.exp (r • L) = NormedSpace.exp ((s + r) • L) := by
  rw [add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl L).smul_left s).smul_right r)]

theorem exp_smul_herm {L : Matrix (Fin n) (Fin n) ℂ} (hL : Lᴴ = L) (s : ℝ) :
    (NormedSpace.exp (s • L))ᴴ = NormedSpace.exp (s • L) := by
  rw [← Matrix.exp_conjTranspose, conjTranspose_smul, hL, star_trivial]

theorem wt_exp_smul {L : Matrix (Fin n) (Fin n) ℂ} (hL : L.IsHermitian) (s : ℝ) :
    wt (NormedSpace.exp (s • L)) = ∑ i, Real.exp (2 * s * hL.eigenvalues i) := by
  unfold wt
  rw [exp_smul_herm hL, exp_smul_add, show s + s = 2 * s by ring, trace_exp_smul hL]

theorem wt_root_le {g L : Matrix (Fin n) (Fin n) ℂ} (hL : L.IsHermitian) (he : NormedSpace.exp L = gᴴ * g) {m : ℕ}
    (hm : 0 < m) (hw : 0 < wt g) (hlog : Real.log (wt g) ≤ m) :
    wt (NormedSpace.exp ((1 / (2 * (m : ℝ))) • L)) ≤ n * Real.exp 1 := by
  rw [wt_exp_smul hL]
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have key : ∀ i, Real.exp (2 * (1 / (2 * (m : ℝ))) * hL.eigenvalues i) ≤ Real.exp 1 := by
    intro i
    have h1 : Real.exp (hL.eigenvalues i) ≤ wt g := by
      have e : wt g = ∑ i, Real.exp (1 * hL.eigenvalues i) := by
        rw [← trace_exp_smul hL 1, one_smul, he]; rfl
      rw [e]
      simpa using Finset.single_le_sum (f := fun i => Real.exp (1 * hL.eigenvalues i))
        (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ i)
    have h2 : hL.eigenvalues i ≤ Real.log (wt g) := (Real.le_log_iff_exp_le hw).2 h1
    apply Real.exp_le_exp.2
    rw [show 2 * (1 / (2 * (m : ℝ))) * hL.eigenvalues i = hL.eigenvalues i / m by field_simp, div_le_one hmr]
    linarith
  calc ∑ i, Real.exp (2 * (1 / (2 * (m : ℝ))) * hL.eigenvalues i) ≤ ∑ _i : Fin n, Real.exp 1 :=
        Finset.sum_le_sum fun i _ => key i
    _ = n * Real.exp 1 := by simp

open scoped Matrix.Norms.L2Operator in
theorem herm_exp_injective {A B : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B)
    (h : NormedSpace.exp A = NormedSpace.exp B) : A = B := by
  rw [← CFC.log_exp A hA, ← CFC.log_exp B hB, h]

def signUnit (ε : Fin n → Bool) : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨Jm ε, Jm ε, Jm_mul_self ε, Jm_mul_self ε⟩

theorem exp_sign_conj (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (Jm ε * A * Jm ε) = Jm ε * NormedSpace.exp A * Jm ε :=
  Matrix.exp_units_conj' (signUnit ε) A

theorem sign_sign_mul (x : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * x) = x := by
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

theorem left_inv_of_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : Jm ε * gᴴ * Jm ε * g = 1 := by
  calc Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, Jm_mul_self]

theorem right_inv_of_inUJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g * (Jm ε * gᴴ * Jm ε) = 1 :=
  mul_eq_one_comm.mp (left_inv_of_inUJ hg)

theorem sign_conj_log {g L : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hL : Lᴴ = L)
    (he : NormedSpace.exp L = gᴴ * g) : Jm ε * L * Jm ε = -L := by
  refine herm_exp_injective ?_ ?_ ?_
  · rw [conjTranspose_mul, conjTranspose_mul, Jm_conjTranspose, hL, Matrix.mul_assoc]
  · rw [conjTranspose_neg, hL]
  · rw [exp_sign_conj, he, Matrix.exp_neg, he]
    refine (Matrix.inv_eq_left_inv ?_).symm
    calc Jm ε * (gᴴ * g) * Jm ε * (gᴴ * g) = (Jm ε * gᴴ) * (g * (Jm ε * gᴴ * Jm ε)) * (Jm ε * g) := by
          simp only [Matrix.mul_assoc, sign_sign_mul]
      _ = 1 := by rw [right_inv_of_inUJ hg, Matrix.mul_one, ← Matrix.mul_assoc]; exact left_inv_of_inUJ hg

theorem exp_log_inUJ {g L : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hL : Lᴴ = L)
    (he : NormedSpace.exp L = gᴴ * g) (s : ℝ) : inUJ ε (NormedSpace.exp (s • L)) := by
  unfold inUJ
  have hJE : Jm ε * NormedSpace.exp (s • L) * Jm ε = NormedSpace.exp ((-s) • L) := by
    rw [← exp_sign_conj, Matrix.mul_smul, Matrix.smul_mul, sign_conj_log hg hL he, smul_neg, neg_smul]
  rw [exp_smul_herm hL]
  calc NormedSpace.exp (s • L) * Jm ε * NormedSpace.exp (s • L)
      = Jm ε * (Jm ε * NormedSpace.exp (s • L) * Jm ε) * NormedSpace.exp (s • L) := by
        simp only [Matrix.mul_assoc, sign_sign_mul]
    _ = Jm ε := by
        rw [hJE, Matrix.mul_assoc, exp_smul_add, neg_add_cancel, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]

theorem mem_Kset_of_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) (hu : kᴴ * k = 1) : k ∈ Kset ε := by
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 hu, ?_⟩
  have h1 : k * kᴴ = 1 := mul_eq_one_comm.mp hu
  calc k * Jm ε = k * (kᴴ * Jm ε * k) := by rw [hk]
    _ = (k * kᴴ) * Jm ε * k := by simp only [Matrix.mul_assoc]
    _ = Jm ε * k := by rw [h1, Matrix.one_mul]

theorem polyGrowth_of_isometric_on_K : ∀ {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε))
    (hK : ∀ k ∈ Kset ε, ∀ v, ‖π k v‖ = ‖v‖),
    ∃ C b : ℝ, 0 < C ∧ 0 ≤ b ∧ ∀ g ∈ UJset ε, ∀ x, ‖π g x‖ ≤ C * wt g ^ b * ‖x‖ := by
  intro n ε H _ _ _ π hrep hc hK
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, 0, one_pos, le_rfl, fun g _ x => ?_⟩
    have hg1 : g = 1 := Subsingleton.elim _ _
    rw [hg1, hrep.1]; simp
  obtain ⟨B, hB1, hB⟩ := exists_bound_on_compact (π := π) hc (isCompact_wt_le ε ((n : ℝ) * Real.exp 1))
    (fun h hh => hh.1)
  have hB0 : 0 < B := by linarith
  refine ⟨B ^ 2, Real.log B, by positivity, Real.log_nonneg hB1, fun g hg x => ?_⟩
  have hg' : inUJ ε g := hg
  have hw : 1 ≤ wt g := one_le_wt hg' ⟨0, hn⟩
  have hw0 : 0 < wt g := by linarith
  have hlog0 : 0 ≤ Real.log (wt g) := Real.log_nonneg hw
  obtain ⟨L, -, hLs, hLe, -⟩ := GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial n g (isUnit_of_inUJ' hg')
  have hLh : L.IsHermitian := hLs
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈Real.log (wt g)⌉₊ + 1 := ⟨_, rfl⟩
  have hm0 : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm0
  have hml : Real.log (wt g) ≤ m := by
    rw [hm]; push_cast; linarith [Nat.le_ceil (Real.log (wt g))]
  have hmu : (m : ℝ) ≤ Real.log (wt g) + 2 := by
    rw [hm]; push_cast; linarith [Nat.ceil_lt_add_one hlog0]
  obtain ⟨h, hh⟩ : ∃ h, h = NormedSpace.exp ((1 / (2 * (m : ℝ))) • L) := ⟨_, rfl⟩
  have hhU : inUJ ε h := hh ▸ exp_log_inUJ hg' hLs hLe _
  have hhS : ‖π h‖ ≤ B := hB h ⟨hhU, hh ▸ wt_root_le hLh hLe hm0 hw0 hml⟩
  obtain ⟨hPU, hPb⟩ := pow_bound hrep hhU hB0.le hhS m
  have hP : h ^ m = NormedSpace.exp ((1 / 2 : ℝ) • L) := by
    rw [hh, ← Matrix.exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = NormedSpace.exp ((-(1 / 2) : ℝ) • L) := ⟨_, rfl⟩
  have hQU : inUJ ε Q := hQ ▸ exp_log_inUJ hg' hLs hLe _
  have hk : inUJ ε (g * Q) := inUJ_mul hg' hQU
  have hku : (g * Q)ᴴ * (g * Q) = 1 := by
    have hQh : Qᴴ = Q := by rw [hQ]; exact exp_smul_herm hLs _
    rw [conjTranspose_mul, hQh]
    calc Q * gᴴ * (g * Q) = Q * (gᴴ * g) * Q := by simp only [Matrix.mul_assoc]
      _ = NormedSpace.exp ((-(1 / 2) : ℝ) • L) * NormedSpace.exp ((1 : ℝ) • L) * NormedSpace.exp ((-(1 / 2) : ℝ) • L) := by
          rw [one_smul, hLe, hQ]
      _ = 1 := by
          rw [exp_smul_add, exp_smul_add, show (-(1 / 2) + 1 + -(1 / 2) : ℝ) = 0 by norm_num, zero_smul,
            NormedSpace.exp_zero]
  have hgk : (g * Q) * h ^ m = g := by
    rw [hP, hQ, Matrix.mul_assoc, exp_smul_add, show (-(1 / 2) + 1 / 2 : ℝ) = 0 by norm_num, zero_smul,
      NormedSpace.exp_zero, Matrix.mul_one]
  have e1 : π g x = π (g * Q) (π (h ^ m) x) := by
    calc π g x = π ((g * Q) * h ^ m) x := by rw [hgk]
      _ = _ := by rw [hrep.2 _ hk _ hPU]; rfl
  rw [e1, hK _ (mem_Kset_of_unitary hk hku)]
  refine (hPb x).trans ?_
  have hfin : B ^ m ≤ B ^ 2 * wt g ^ Real.log B := by
    rw [← Real.rpow_natCast B m]
    calc B ^ (m : ℝ) ≤ B ^ (Real.log (wt g) + 2) := Real.rpow_le_rpow_of_exponent_le hB1 hmu
      _ = B ^ 2 * wt g ^ Real.log B := by
          rw [add_comm, Real.rpow_add hB0, Real.rpow_two, Real.rpow_def_of_pos hB0 (Real.log (wt g)),
            Real.rpow_def_of_pos hw0 (Real.log B), mul_comm (Real.log B)]
  exact mul_le_mul_of_nonneg_right hfin (norm_nonneg x)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.PolyGrowth

end
end

section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Volume

open MeasureTheory

theorem wt_eq_hs {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : wt M = Formalism.REAL.hs M := by
  have key : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    have h : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  unfold wt Formalism.REAL.hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, key]
  exact Finset.sum_comm

theorem one_le_hs_of_inUJ {n : ℕ} (hn : 0 < n) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ)
    (h : Formalism.REAL.inUJ ε g) : 1 ≤ Formalism.REAL.hs g := by
  set a : Fin n := ⟨0, hn⟩ with ha
  have hs1 : ∀ k : Fin n, ‖(if ε k = true then (1 : ℂ) else -1)‖ = 1 := by
    intro k; split_ifs <;> simp
  have e : ∑ k, star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a =
      (if ε a = true then (1 : ℂ) else -1) := by
    have h2 := congrFun (congrFun h a) a
    simpa [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal_apply] using h2
  have h3 : (1 : ℝ) ≤ ∑ k, ‖g k a‖ ^ 2 := by
    calc (1 : ℝ) = ‖∑ k, star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a‖ := by
          rw [e, hs1]
      _ ≤ ∑ k, ‖star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a‖ := norm_sum_le _ _
      _ = ∑ k, ‖g k a‖ ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul, hs1, norm_star]; ring
  refine h3.trans ?_
  unfold Formalism.REAL.hs
  refine Finset.sum_le_sum fun k _ => ?_
  exact Finset.single_le_sum (f := fun j => ‖g k j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ a)

theorem rpow_neg_le_of_dichotomy {w b' : ℝ} {s : ℕ} (hw : w = 0 ∨ 1 ≤ w) (hb : (s : ℝ) ≤ b') :
    w ^ (-b') ≤ ((2 : ℝ) ^ b' + 1) * ((1 + w)⁻¹) ^ s := by
  have hb0 : 0 ≤ b' := (Nat.cast_nonneg s).trans hb
  have h2 : (0 : ℝ) < (2 : ℝ) ^ b' := Real.rpow_pos_of_pos (by norm_num) _
  rcases hw with rfl | hw
  · have h1 : (0 : ℝ) ^ (-b') ≤ 1 := Real.zero_rpow_le_one _
    simp only [add_zero, inv_one, one_pow, mul_one]
    linarith
  · have hw0 : 0 < w := by linarith
    have hu0 : 0 < (1 + w)⁻¹ := by positivity
    have hu1 : (1 + w)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hwi : w⁻¹ ≤ 2 * (1 + w)⁻¹ := by
      rw [inv_le_comm₀ hw0 (by positivity), mul_inv, inv_inv]
      linarith
    calc w ^ (-b') = (w⁻¹) ^ b' := by rw [Real.rpow_neg hw0.le, Real.inv_rpow hw0.le]
      _ ≤ (2 * (1 + w)⁻¹) ^ b' := Real.rpow_le_rpow (by positivity) hwi hb0
      _ = (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ b' := Real.mul_rpow (by norm_num) hu0.le
      _ ≤ (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ (s : ℝ) := by
          gcongr ?_ * ?_
          exact Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hb
      _ = (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ s := by rw [Real.rpow_natCast]
      _ ≤ _ := by
          have : 0 ≤ ((1 + w)⁻¹) ^ s := by positivity
          nlinarith

theorem integrable_wt_rpow_neg {n : ℕ} (ε : Fin n → Bool) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ b' : ℝ, b ≤ b' →
      MeasureTheory.Integrable (fun g : UJ ε => wt (uMat g) ^ (-b')) (Formalism.REAL.muG ε).inv := by
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.HolPQ.one_add_hs_inv_pow_lintegral_lt_top n ε
  have hfin : ∫⁻ g : UJ ε, ENNReal.ofReal (((1 + Formalism.REAL.hs (uMat g))⁻¹) ^ s) ∂(Formalism.REAL.muG ε) < ⊤ :=
    hs s le_rfl
  refine ⟨s, Nat.cast_nonneg s, fun b' hb' => ?_⟩
  have hinv : (Formalism.REAL.muG ε).inv = Formalism.REAL.muG ε := Formalism.REAL.invInvariant n ε
  rw [hinv]
  have hc : Continuous fun g : UJ ε => Formalism.REAL.hs (uMat g) := GlobalTheory.CompanionTheory.HolPQ.continuous_hs_umat ε
  have hnn : ∀ g : UJ ε, 0 ≤ Formalism.REAL.hs (uMat g) := fun g =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hI : Integrable (fun g : UJ ε => ((1 + Formalism.REAL.hs (uMat g))⁻¹) ^ s) (Formalism.REAL.muG ε) := by
    refine ⟨((measurable_const.add hc.measurable).inv.pow_const s).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun g => by
      have := hnn g
      positivity)]
    exact hfin
  have hw : ∀ g : UJ ε, wt (uMat g) = Formalism.REAL.hs (uMat g) := fun g => wt_eq_hs _
  have hmeas : Measurable fun g : UJ ε => wt (uMat g) ^ (-b') := by
    simp only [hw]
    exact hc.measurable.pow_const _
  refine (hI.const_mul ((2 : ℝ) ^ b' + 1)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  have hdich : Formalism.REAL.hs (uMat g) = 0 ∨ 1 ≤ Formalism.REAL.hs (uMat g) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp [Formalism.REAL.hs]
    · right; exact one_le_hs_of_inUJ hn ε _ g.2
  rw [hw, Real.norm_of_nonneg (Real.rpow_nonneg (hnn g) _)]
  exact rpow_neg_le_of_dichotomy hdich hb'

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Volume

end
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi

theorem exists_unitary_iwasawa_leviOne : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}
    (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i), ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ g ∈ mats (leviOne ε W), ∃ k ∈ maxCpt (mats (leviOne ε W)), ∃ s ∈ mats (leviOne ε W),
        g = k * s ∧ (Uᴴ * s * U).BlockTriangular id :=
  fun {_ _ ε j W} hW hj => GlobalTheory.CompanionTheory.LeviIwa.iwaOn_leviOne ε j W hW hj

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi

end
end

section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open MeasureTheory CompanionTheory.D.gk.admitted
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.admitted

variable {n : ℕ}

def grp {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℂ) ∈ G}
  mul_mem' := fun {a b} ha hb => hG.mul_mem _ ha _ hb
  one_mem' := hG.one_mem
  inv_mem' := fun {u} hu => by
    show ((u⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ G
    rw [Matrix.coe_units_inv]
    exact hG.inv_mem _ hu

abbrev toMat {G : Set (Matrix (Fin n) (Fin n) ℂ)} {hG : IsLinRed G} (g : grp hG) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)


theorem continuous_toMat {G : Set (Matrix (Fin n) (Fin n) ℂ)} {hG : IsLinRed G} :
    Continuous (toMat : grp hG → Matrix (Fin n) (Fin n) ℂ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem toMat_injective {G : Set (Matrix (Fin n) (Fin n) ℂ)} {hG : IsLinRed G} :
    Function.Injective (toMat : grp hG → Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem exists_elt {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ G) :
    ∃ g : grp hG, toMat g = m :=
  ⟨⟨(hG.isUnit m hm).unit, hm⟩, rfl⟩

def kgrp {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) : Subgroup (grp hG) where
  carrier := {g | toMat g ∈ Matrix.unitaryGroup (Fin n) ℂ}
  mul_mem' := fun {a b} ha hb => (Matrix.unitaryGroup (Fin n) ℂ).mul_mem ha hb
  one_mem' := (Matrix.unitaryGroup (Fin n) ℂ).one_mem
  inv_mem' := fun {u} hu => by
    have h1 : (toMat u)ᴴ * toMat u = 1 := Matrix.mem_unitaryGroup_iff'.1 hu
    have h2 : toMat u⁻¹ = (toMat u)ᴴ := by
      have h3 : toMat u⁻¹ * toMat u = 1 := by
        show (((u⁻¹ * u : grp hG) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
        simp
      have h4 : toMat u * (toMat u)ᴴ = 1 := mul_eq_one_comm.1 h1
      calc toMat u⁻¹ = toMat u⁻¹ * (toMat u * (toMat u)ᴴ) := by rw [h4, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
    show toMat u⁻¹ ∈ Matrix.unitaryGroup (Fin n) ℂ
    rw [h2]
    exact Unitary.star_mem hu

theorem isCompact_maxCpt {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) : IsCompact (maxCpt G) := by
  have hUc : IsCompact (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    have hcl : IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) = {A | Aᴴ * A = 1} := by
        ext A
        exact Matrix.mem_unitaryGroup_iff'
      rw [this]
      exact isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_closedBall (0 : ℂ) 1) hcl ?_
    intro A hA i _ j _
    simpa using entry_norm_bound_of_unitary hA i j
  refine hUc.of_isClosed_subset ?_ Set.inter_subset_right
  refine isClosed_of_closure_subset fun g hg => ?_
  have hgU : g ∈ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    closure_minimal Set.inter_subset_right hUc.isClosed hg
  have hu : IsUnit g := IsUnit.of_mul_eq_one _ (Matrix.mem_unitaryGroup_iff.1 hgU)
  exact ⟨hG.closed g hu (closure_mono Set.inter_subset_left hg), hgU⟩

instance compactSpace_kgrp {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) : CompactSpace (kgrp hG) := by
  haveI : CompactSpace (maxCpt G) := isCompact_iff_compactSpace.1 (isCompact_maxCpt hG)
  let ψ : maxCpt G → kgrp hG := fun m =>
    ⟨⟨⟨m.1, m.1ᴴ, Matrix.mem_unitaryGroup_iff.1 m.2.2, Matrix.mem_unitaryGroup_iff'.1 m.2.2⟩, m.2.1⟩, by
      show m.1 ∈ Matrix.unitaryGroup (Fin n) ℂ
      exact m.2.2⟩
  have hψ : Continuous ψ := by
    refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩
  refine Function.Surjective.compactSpace (f := ψ) hψ ?_
  rintro ⟨⟨u, hu⟩, hk⟩
  refine ⟨⟨u, hu, hk⟩, ?_⟩
  exact Subtype.ext (Subtype.ext (Units.ext rfl))

instance secondCountable_grp {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G) : SecondCountableTopology (grp hG) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  exact TopologicalSpace.Subtype.secondCountableTopology _

section Core

variable {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def homG (hG : IsLinRed G) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn G σ) :
    grp hG →* (H →L[ℂ] H) where
  toFun g := σ (toMat g)
  map_one' := hσ.1.1
  map_mul' a b := hσ.1.2 _ a.2 _ b.2

def stdU (hG : IsLinRed G) {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    grp hG →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := Uᴴ * toMat g * U
  map_one' := by
    have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    show Uᴴ * 1 * U = 1
    rw [Matrix.mul_one, h1]
  map_mul' a b := by
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    show Uᴴ * (toMat a * toMat b) * U = _
    calc Uᴴ * (toMat a * toMat b) * U = Uᴴ * toMat a * (U * Uᴴ) * toMat b * U := by
          rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_stable [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hI : ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ G, ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id)
    (hσ : IsURepOn G σ) (hirr : IsIrredOn G σ) (S : Submodule ℂ H) [FiniteDimensional ℂ S] (hS : IsKStable G σ S)
    (v : H) (hv : v ∈ S) :
    ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧
      ∀ T : H →L[ℂ] H, (∀ k ∈ maxCpt G, ∀ u, T (σ k u) = σ k (T u)) → ∀ y ∈ Y, T y ∈ Y := by
  obtain ⟨U, hU, hiwa⟩ := hI
  letI : MeasurableSpace (kgrp hG) := borel _
  haveI : BorelSpace (kgrp hG) := ⟨rfl⟩
  let μ : Measure (kgrp hG) := (Measure.haar : Measure (kgrp hG)).inv
  have hμ : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure
  have hsc : SecondCountableTopology (kgrp hG) := TopologicalSpace.Subtype.secondCountableTopology _
  have hiso : ∀ g u, ‖homG hG hσ g u‖ = ‖u‖ := fun g u => hσ.2.1 _ g.2 u
  have hc : ∀ u, Continuous fun g => homG hG hσ g u := fun u =>
    (hσ.2.2 u).comp_continuous continuous_toMat fun g => g.2
  have hKm : ∀ k : kgrp hG, toMat k.1 ∈ maxCpt G := fun k => ⟨k.1.2, k.2⟩
  obtain ⟨e, E, he, hfin, hE, hEv⟩ := exists_averaging_operator (kgrp hG) μ H ((homG hG hσ).comp (kgrp hG).subtype)
    (fun k u => hiso k u) (fun u => (hc u).comp continuous_subtype_val) S (fun k u hu => hS _ (hKm k) u hu) v hv
  choose st hst using fun g : grp hG => exists_elt hG (hG.star_mem _ g.2)
  let Tr : Set (grp hG) := {s | (stdU hG hU s).BlockTriangular id}
  have hgood : IsGood st Tr (stdU hG hU) := by
    refine ⟨(continuous_const.matrix_mul continuous_toMat).matrix_mul continuous_const, fun g => ?_,
      Fin.val, Fin.val_injective, fun s hs i j hij => hs hij⟩
    show Uᴴ * toMat (st g) * U = (Uᴴ * toMat g * U)ᴴ
    rw [hst]
    simp [Matrix.mul_assoc]
  have hinj : Function.Injective (stdU hG hU) := by
    intro a b hab
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    have key : ∀ g : grp hG, U * stdU hG hU g * Uᴴ = toMat g := fun g => by
      show U * (Uᴴ * toMat g * U) * Uᴴ = _
      calc U * (Uᴴ * toMat g * U) * Uᴴ = (U * Uᴴ) * toMat g * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    exact toMat_injective ((key a).symm.trans (hab ▸ key b))
  have hKS : ∀ g : grp hG, ∃ k ∈ kgrp hG, ∃ s ∈ Tr, g = k * s := by
    intro g
    obtain ⟨k, hk, s, hs, hg, ht⟩ := hiwa (toMat g) g.2
    obtain ⟨k', rfl⟩ := exists_elt hG hk.1
    obtain ⟨s', rfl⟩ := exists_elt hG hs
    exact ⟨k', hk.2, s', ht, toMat_injective hg⟩
  have hPI : ∀ g : Fin (Module.finrank ℂ S ^ 2 + 1) → grp hG, stdPoly E (fun i => homG hG hσ (g i)) = 0 := fun g =>
    transfer_holds (grp hG) (kgrp hG) μ st Tr (Fin n) (stdU hG hU) hgood hinj e he _ g
      (fun ι _ _ ρ hρ E' hE' => goodPI_of small_irreducible_representation (grp hG) (kgrp hG) μ st Tr hKS e _ _ he hfin
        (Nat.lt_succ_self _) ι ρ hρ E' hE' g)
      H (homG hG hσ) hc E hE
  obtain ⟨hfd, -⟩ := finite_rank_of_irreducible_unitary (grp hG) H (homG hG hσ) hiso (fun S' hcl hS' => hirr S' hcl fun g hg u hu => by
    obtain ⟨g, rfl⟩ := exists_elt hG hg
    exact hS' g u hu) E _ hPI
  refine ⟨_, hfd, ⟨v, hEv⟩, ?_⟩
  rintro T hT _ ⟨u, rfl⟩
  refine ⟨T u, ?_⟩
  show E (T u) = T (E u)
  rw [hE, hE, ← T.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show e k • σ (toMat k.1) (T u) = T (e k • σ (toMat k.1) u)
    rw [map_smul, hT _ (hKm k)]
  · exact (he.smul ((hc u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end Core

theorem isAdmOn_of_iwasawa {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hI : ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ G, ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id)
    (hU : IsURepOn G π) (hirr : IsIrredOn G π) : IsAdmOn G π := by
  refine ⟨hU.1, hU.2.2, fun k hk => hU.2.1 k hk.1, ?_⟩
  intro S hfd hS _
  haveI := hfd
  let b := Module.finBasis ℂ S
  choose Y hYfd hvY hY using fun i => exists_stable hG hI hU hirr S hS (b i) (b i).2
  haveI := hYfd
  have hsup : FiniteDimensional ℂ (⨆ i, Y i : Submodule ℂ H) := Submodule.finiteDimensional_iSup Y
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Y i) (sSup_le ?_)
  rintro _ ⟨Θ₀, rfl, hΘ⟩
  let Θ : S →ₗ[ℂ] H := Θ₀.domRestrict S
  let T : H →L[ℂ] H := (LinearMap.toContinuousLinearMap Θ).comp S.orthogonalProjectionOnto
  have hT : ∀ k ∈ maxCpt G, ∀ u, T (π k u) = π k (T u) := by
    intro k hk u
    have hkG := hk.1
    have hk1 : k * k.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    have hks : k.conjTranspose ∈ maxCpt G := ⟨hG.star_mem _ hkG, Unitary.star_mem hk.2⟩
    have hiso : ∀ x y, ⟪π k x, π k y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y =>
      (LinearIsometry.mk (π k : H →ₗ[ℂ] H) (hU.2.1 k hkG)).inner_map_map x y
    have hP : ((S.orthogonalProjectionOnto (π k u) : S) : H) = π k (S.orthogonalProjectionOnto u : S) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.orthogonalProjectionOnto u).2) ?_
      intro w hw
      have hw' : π k (π k.conjTranspose w) = w := by
        rw [← ContinuousLinearMap.comp_apply, ← hU.1.2 _ hkG _ hks.1, hk1, hU.1.1]
        rfl
      rw [← hw', ← map_sub, hiso]
      exact S.starProjection_inner_eq_zero u _ (hS _ hks w hw)
    show Θ₀ ((S.orthogonalProjectionOnto (π k u) : S) : H) = π k (Θ₀ (S.orthogonalProjectionOnto u : S))
    rw [hP]
    exact hΘ k hk _ (S.orthogonalProjectionOnto u).2
  rintro _ ⟨v, hv, rfl⟩
  have hv2 : v = ∑ i, b.repr ⟨v, hv⟩ i • (b i : H) := by
    calc v = ((∑ i, b.repr ⟨v, hv⟩ i • b i : S) : H) := by rw [b.sum_repr]
      _ = _ := (map_sum S.subtype _ _).trans (Finset.sum_congr rfl fun i _ => rfl)
  show Θ₀ v ∈ _
  rw [hv2, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ?_)
  have := hY i T hT _ (hvY i)
  simpa [T, Θ] using this

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.admitted

end
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis

variable {n : ℕ}

def vecOf : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℝ] EuclideanSpace ℂ (Fin n × Fin n) where
  toFun X := WithLp.toLp 2 (fun p => X p.1 p.2)
  invFun x := Matrix.of fun i j => x (i, j)
  map_add' X Y := by ext p; simp
  map_smul' r X := by ext p; simp
  left_inv X := by ext i j; simp
  right_inv x := by ext p; simp

theorem inner_vecOf (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf X, vecOf Y⟫_ℝ = (Xᴴ * Y).trace.re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [vecOf, Complex.inner]
  ring

theorem inner_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    ⟪vecOf (k * X * k⁻¹), vecOf (k * Y * k⁻¹)⟫_ℝ = ⟪vecOf X, vecOf Y⟫_ℝ := by
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk
  have h2 : k * kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hk
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_right_inv h2
  rw [inner_vecOf, inner_vecOf, hinv]
  have : (k * X * kᴴ)ᴴ * (k * Y * kᴴ) = k * (Xᴴ * Y) * kᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc k * (Xᴴ * kᴴ) * (k * Y * kᴴ) = k * Xᴴ * (kᴴ * k) * Y * kᴴ := by
          simp only [Matrix.mul_assoc]
      _ = k * (Xᴴ * Y) * kᴴ := by rw [h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem exists_orthonormal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (W : Submodule ℝ E)
    [FiniteDimensional ℝ W] :
    ∃ (d : ℕ) (e : Fin d → E), (∀ i, e i ∈ W) ∧ Orthonormal ℝ e ∧ ∀ x ∈ W, x = ∑ i, ⟪e i, x⟫_ℝ • e i := by
  let B := stdOrthonormalBasis ℝ W
  refine ⟨_, fun i => (B i : E), fun i => (B i).2, ?_, ?_⟩
  · exact B.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  · intro x hx
    have := congrArg (Subtype.val) (B.sum_repr' ⟨x, hx⟩)
    simpa [Submodule.coe_sum] using this.symm

theorem orthogonal_of_preserves {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ} {e : Fin d → E}
    (he : Orthonormal ℝ e) (f : Fin d → E) (hexp : ∀ i, f i = ∑ l, ⟪e l, f i⟫_ℝ • e l)
    (hf : ∀ i j, ⟪f i, f j⟫_ℝ = ⟪e i, e j⟫_ℝ) :
    (Matrix.of fun l i => ⟪e l, f i⟫_ℝ : Matrix (Fin d) (Fin d) ℝ)ᵀ * Matrix.of (fun l i => ⟪e l, f i⟫_ℝ) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  have h : ⟪f i, f j⟫_ℝ = ∑ l, ⟪e l, f i⟫_ℝ * ⟪e l, f j⟫_ℝ := by
    conv_lhs => rw [hexp j]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_right, mul_comm, real_inner_comm (e l) (f i)]
  rw [← h, hf, orthonormal_iff_ite.1 he, Matrix.one_apply]

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis

open GlobalTheory.CompanionTheory.Hypotheses₂.HCA.InvBasis in

theorem GlobalTheory.CompanionTheory.Hypotheses₂.HCA.exists_basis_lieOf_orthogonal : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (_hG : IsLinRed G), ∃ (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, b i ∈ HCSS.lieOf G) ∧ LinearIndependent ℝ b ∧ (∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) ∧ ∀ k ∈ maxCpt G, ∃ O : Matrix (Fin d) (Fin d) ℝ, Oᵀ * O = 1 ∧ ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l := by
  intro n G hG
  obtain ⟨hadd, hsmul, -, hAd⟩ := lieOf_isLieSubalgebra hG
  let L : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := HCSS.lieOf G
      add_mem' := fun {X Y} hX hY => hadd X Y hX hY
      zero_mem' := fun t => by simpa using hG.one_mem
      smul_mem' := fun r X hX => hsmul r X hX }
  let W : Submodule ℝ (EuclideanSpace ℂ (Fin n × Fin n)) := L.map (vecOf (n := n)).toLinearMap
  have : FiniteDimensional ℝ (EuclideanSpace ℂ (Fin n × Fin n)) :=
    FiniteDimensional.complexToReal _
  obtain ⟨d, e, heW, hon, hexp⟩ := exists_orthonormal W
  have hmemW : ∀ X ∈ HCSS.lieOf G, vecOf X ∈ W := fun X hX => ⟨X, hX, rfl⟩
  have hbL : ∀ i, vecOf.symm (e i) ∈ HCSS.lieOf G := by
    intro i
    obtain ⟨X, hX, hXe⟩ := heW i
    have : vecOf.symm (e i) = X := by
      rw [← hXe]; simp
    rw [this]; exact hX
  have hexpM : ∀ X ∈ HCSS.lieOf G, X = ∑ i, ⟪e i, vecOf X⟫_ℝ • vecOf.symm (e i) := by
    intro X hX
    have h := hexp _ (hmemW X hX)
    have h2 := congrArg (vecOf (n := n)).symm h
    rw [map_sum] at h2
    simpa using h2
  refine ⟨d, fun i => vecOf.symm (e i), hbL, ?_, ?_, ?_⟩
  · exact hon.linearIndependent.map' (vecOf (n := n)).symm.toLinearMap
      (LinearMap.ker_eq_bot.2 (vecOf (n := n)).symm.injective)
  · intro X hX
    exact ⟨_, hexpM X hX⟩
  · intro k hk
    have hkG : k ∈ G := hk.1
    have hkU : k ∈ Matrix.unitaryGroup (Fin n) ℂ := hk.2
    let f : Fin d → EuclideanSpace ℂ (Fin n × Fin n) := fun i => vecOf (k * vecOf.symm (e i) * k⁻¹)
    have hfW : ∀ i, f i ∈ W := fun i => hmemW _ (hAd k hkG _ (hbL i))
    have hO := orthogonal_of_preserves hon f (fun i => hexp _ (hfW i)) (fun i j => by
      have := inner_conj hkU (vecOf.symm (e i)) (vecOf.symm (e j))
      simpa [f] using this)
    refine ⟨_, hO, fun i => ?_⟩
    have h := hexp _ (hfW i)
    have h2 := congrArg (vecOf (n := n)).symm h
    rw [map_sum] at h2
    simpa [f] using h2

end
end

section
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem differentiableAt_entries_exp_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    DifferentiableAt ℝ
      (fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ)) s := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) _ s :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X s
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  exact (L.hasFDerivAt.comp_hasDerivAt s hc).differentiableAt

theorem dRep_equivariant : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G), π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v) := by
  intro n G H _ _ π hG hrep v hv X hX g hg
  obtain ⟨F, hF, hFv⟩ := hv
  have hu : IsUnit g := hG.isUnit g hg
  have hgi : g⁻¹ ∈ G := hG.inv_mem g hg
  have hinv : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).1 hu)
  have hd : DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0 := by
    have he : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) =
        F ∘ fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ) := by
      funext t
      exact hFv _ (hX t)
    rw [he]
    exact (hF.differentiable (by simp)).differentiableAt.comp 0
      (differentiableAt_entries_exp_smul X 0)
  have key : ∀ t : ℝ, π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v) =
      π g (π (NormedSpace.exp (t • X)) v) := by
    intro t
    have hconj : NormedSpace.exp (t • (g * X * g⁻¹)) = g * NormedSpace.exp (t • X) * g⁻¹ := by
      have : t • (g * X * g⁻¹) = g * (t • X) * g⁻¹ := by
        simp [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
      rw [this, Matrix.exp_conj _ _ hu]
    have hge : g * NormedSpace.exp (t • X) ∈ G := hG.mul_mem _ hg _ (hX t)
    have h1 : π (g * NormedSpace.exp (t • X) * g⁻¹ * g) =
        (π (g * NormedSpace.exp (t • X) * g⁻¹)).comp (π g) :=
      hrep.2 _ (hG.mul_mem _ hge _ hgi) _ hg
    have h2 : g * NormedSpace.exp (t • X) * g⁻¹ * g = g * NormedSpace.exp (t • X) := by
      rw [Matrix.mul_assoc _ g⁻¹ g, hinv, Matrix.mul_one]
    have h3 := hrep.2 _ hg _ (hX t)
    rw [hconj]
    rw [h2, h3] at h1
    exact (DFunLike.congr_fun h1 v).symm
  have h2 := ((π g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
  have h3 : deriv (fun t : ℝ => π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v)) 0 =
      π g (deriv (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0) := by
    rw [funext key]
    exact h2.deriv
  exact h3.symm

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
end

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derived_action_conjugation : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G), π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem dRep_realSum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u : H} (hu : IsSmoothVec G π u) {ι : Type} (s : Finset ι)
    (c : ι → ℝ) (a : ι → Matrix (Fin n) (Fin n) ℂ) (ha : ∀ l, a l ∈ HCSS.lieOf G)
    (h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ HCSS.lieOf G) :
    (∑ l ∈ s, c l • a l) ∈ HCSS.lieOf G ∧
      dRep π (∑ l ∈ s, c l • a l) u = ∑ l ∈ s, c l • dRep π (a l) u := by
  classical
  obtain ⟨hadd, hsm, -, -⟩ := GlobalTheory.T.lie_algebra_of_linear_group_closed hG
  induction s using Finset.induction_on with
  | empty => simpa using ⟨h0, GlobalTheory.GKLie.dRep_zero π u⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 := hsm (c x) _ (ha x)
    refine ⟨hadd _ _ h1 ih.1, ?_⟩
    rw [(GlobalTheory.T.derived_action_additive hG hrep hu hu h1 ih.1).1, ih.2, GlobalTheory.GKLie.dRep_smul]

theorem dRep_vecSum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G)
    {ι : Type} (s : Finset ι) (c : ι → ℝ) (u : ι → H) (hu : ∀ l, IsSmoothVec G π (u l)) :
    IsSmoothVec G π (∑ l ∈ s, c l • u l) ∧
      dRep π X (∑ l ∈ s, c l • u l) = ∑ l ∈ s, c l • dRep π X (u l) := by
  classical
  obtain ⟨hadd, hsm, -⟩ := GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, by simp [dRep]⟩
    exact ⟨fun _ => 0, contDiff_const, fun z _ => by simp⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 : IsSmoothVec G π (c x • u x) := by
      rw [← Complex.coe_smul]
      exact hsm _ _ (hu x)
    refine ⟨hadd _ _ h1 ih.1, ?_⟩
    rw [(GlobalTheory.T.derived_action_additive hG hrep h1 ih.1 hX hX).2.1, ih.2, ← Complex.coe_smul,
      (GlobalTheory.T.derived_action_additive hG hrep (hu x) (hu x) hX hX).2.2, Complex.coe_smul]

theorem sumSquares_comm {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ G)
    (O : Matrix (Fin d) (Fin d) ℝ) (hO : Oᵀ * O = 1) (hkb : ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l)
    {v : H} (hv : IsSmoothVec G π v) :
    π k (∑ i, dRep π (b i) (dRep π (b i) v)) = ∑ i, dRep π (b i) (dRep π (b i) (π k v)) := by
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i0⟩⟩
  · simp [Finset.univ_eq_empty]
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ HCSS.lieOf G := by
    simpa using (GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.1 0 _ (hb i0)
  have hw : IsSmoothVec G π (π k v) := (GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep).2.2 k hk v hv
  have hT : ∀ m, IsSmoothVec G π (dRep π (b m) (π k v)) := fun m =>
    (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hw (hb m)).2
  have step : ∀ i, π k (dRep π (b i) (dRep π (b i) v)) =
      ∑ l, ∑ m, (O l i * O m i) • dRep π (b l) (dRep π (b m) (π k v)) := by
    intro i
    have hsm := (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hv (hb i)).2
    rw [GlobalTheory.T.derived_action_conjugation hG hrep hsm (hb i) hk, GlobalTheory.T.derived_action_conjugation hG hrep hv (hb i) hk, hkb i,
      (dRep_realSum hG hrep hw Finset.univ (fun m => O m i) b hb h0).2,
      (dRep_realSum hG hrep
        (dRep_vecSum hG hrep (hb i0) Finset.univ (fun m => O m i) _ hT).1
        Finset.univ (fun l => O l i) b hb h0).2]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(dRep_vecSum hG hrep (hb l) Finset.univ (fun m => O m i) _ hT).2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.1 hO
  have hdelta : ∀ l m, ∑ i, O l i * O m i = (1 : Matrix (Fin d) (Fin d) ℝ) l m := fun l m => by
    rw [← hOO]
    simp [Matrix.mul_apply]
  rw [map_sum, Finset.sum_congr rfl fun i _ => step i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hdelta, Matrix.one_apply]
  simp

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mnorm_real_smul (s : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : mnorm (s • X) = |s| * mnorm X := by
  unfold mnorm
  simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, Finset.mul_sum]

theorem mnorm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem iterate_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hs : IsSmoothVec G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    IsSmoothVec G π ((dRep π X)^[m] v) := by
  induction m with
  | zero => simpa using hs
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (GlobalTheory.T.derived_action_of_smooth_vector hG hrep ih hX).2

theorem iterate_real_smul (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hs : IsSmoothVec G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (s : ℝ) (m : ℕ) :
    (dRep π (s • X))^[m] v = ((s : ℂ) ^ m) • (dRep π X)^[m] v := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsm := iterate_smooth hG hrep hs hX m
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', GlobalTheory.GKLie.dRep_smul,
      (GlobalTheory.T.derived_action_additive hG hrep hsm hsm hX hX).2.2, ← Complex.coe_smul, smul_smul, pow_succ']

theorem analytic_coeff : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hU : IsURepOn G π) {v : H} (hs : IsSmoothVec G π v) (hw : WordBound G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (w : H),
    AnalyticOnNhd ℝ (fun t : ℝ => ⟪w, π (NormedSpace.exp (t • X)) v⟫_ℂ) Set.univ := by
  intro n G H _ _ _ π hG hU v hs hw X hX w t₀ _
  obtain ⟨r, hr, hsum⟩ := GlobalTheory.T.analytic_vector_exponential_series hG hU.1 hU.2.2 hs hw
  have hrep := hU.1
  let L : H →L[ℂ] ℂ := (innerSL ℂ w).comp (π (NormedSpace.exp (t₀ • X)))
  let a : ℕ → ℂ := fun m => ((m.factorial : ℂ)⁻¹) * L ((dRep π X)^[m] v)
  have key : ∀ s : ℝ, |s| * mnorm X < r → HasSum (fun m : ℕ => (s : ℂ) ^ m * a m)
      (⟪w, π (NormedSpace.exp ((t₀ + s) • X)) v⟫_ℂ) := by
    intro s hs'
    have h1 := hsum (s • X) ((GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.1 s X hX) (by rwa [mnorm_real_smul])
    have h2 := L.hasSum h1
    have e : ⟪w, π (NormedSpace.exp ((t₀ + s) • X)) v⟫_ℂ = L (π (NormedSpace.exp (s • X)) v) := by
      have hc : Commute (t₀ • X) (s • X) := ((Commute.refl X).smul_left t₀).smul_right s
      rw [add_smul, Matrix.exp_add_of_commute _ _ hc, hrep.2 _ (hX t₀) _ (hX s)]
      rfl
    rw [e]
    convert h2 using 2 with m
    rw [iterate_real_smul hG hrep hs hX s m]
    simp only [a, map_smul, smul_eq_mul]
    ring
  let p : FormalMultilinearSeries ℝ ℝ ℂ := fun m => ContinuousMultilinearMap.mkPiRing ℝ (Fin m) (a m)
  have hpa : ∀ (m : ℕ) (s : ℝ), p m (fun _ => s) = (s : ℂ) ^ m * a m := by
    intro m s
    simp [p, ContinuousMultilinearMap.mkPiRing_apply]
  have hM : 0 < mnorm X + 1 := by linarith [mnorm_nonneg X]
  have hsmall : ∀ s : ℝ, |s| < r / (mnorm X + 1) → |s| * mnorm X < r := by
    intro s h
    rw [lt_div_iff₀ hM] at h
    nlinarith [abs_nonneg s]
  set ε : ℝ := r / (mnorm X + 1) with hε
  have hεpos : 0 < ε := div_pos hr hM
  have hrad : 0 < p.radius := by
    have hs0 : |ε / 2| < ε := by rw [abs_of_pos (by linarith)]; linarith
    have hS := (key (ε / 2) (hsmall _ hs0)).summable.norm
    let ρ : NNReal := ⟨ε / 2, by linarith⟩
    have hρ : (0 : NNReal) < ρ := by
      change (0 : ℝ) < ε / 2
      linarith
    have : (ρ : ENNReal) ≤ p.radius := by
      refine p.le_radius_of_summable_norm ?_
      refine hS.congr fun m => ?_
      have hρc : ((ρ : NNReal) : ℝ) = ε / 2 := rfl
      simp [p, hρc, ContinuousMultilinearMap.norm_mkPiRing, abs_of_pos hεpos, mul_comm]
    exact lt_of_lt_of_le (by exact_mod_cast hρ) this
  have han : AnalyticAt ℝ p.sum 0 := (p.hasFPowerSeriesOnBall hrad).analyticAt
  have han2 : AnalyticAt ℝ (fun t : ℝ => p.sum (t - t₀)) t₀ :=
    AnalyticAt.comp_of_eq (g := p.sum) (f := fun t : ℝ => t - t₀) han
      (analyticAt_id.sub analyticAt_const) (by simp)
  refine han2.congr ?_
  filter_upwards [Metric.ball_mem_nhds t₀ hεpos] with t ht
  have hd : |t - t₀| < ε := by simpa [Real.dist_eq] using ht
  have h3 := key (t - t₀) (hsmall _ hd)
  rw [show t₀ + (t - t₀) = t by ring] at h3
  simp only [FormalMultilinearSeries.sum, hpa]
  exact h3.tsum_eq

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam

end
end

section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem isotypic : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hA : IsAdmOn G π) {v : H} (hv : IsKFinOn G π v), ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ IsKStable G π Y ∧ ∀ D : Y →ₗ[ℂ] H, (∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y)) → ∀ y, D y ∈ Y :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic.exists_isotypic_sum

theorem garding : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hcl : IsClosed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) (hK : ∀ k ∈ maxCpt G, ∀ v, ‖π k v‖ = ‖v‖) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (hY : ∀ T : H →L[ℂ] H, (∀ k ∈ maxCpt G, ∀ u, T (π k u) = π k (T u)) → ∀ y ∈ Y, T y ∈ Y), ∀ v ∈ Y, IsSmoothVec G π v :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Gard.smooth_of_commutant_stable

theorem growth : ∀ {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) (hK : ∀ k ∈ Kset ε, ∀ v, ‖π k v‖ = ‖v‖), ∃ C b : ℝ, 0 < C ∧ 0 ≤ b ∧ ∀ g ∈ UJset ε, ∀ x, ‖π g x‖ ≤ C * wt g ^ b * ‖x‖ :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.PolyGrowth.polyGrowth_of_isometric_on_K

theorem volume : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ b : ℝ, 0 ≤ b ∧ ∀ b' : ℝ, b ≤ b' → MeasureTheory.Integrable (fun g : UJ ε => wt (uMat g) ^ (-b')) (Formalism.REAL.muG ε).inv :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Volume.integrable_wt_rpow_neg

theorem almost_of_growth : ∀ {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) (hg : ∃ C b : ℝ, 0 < C ∧ 0 ≤ b ∧ ∀ g ∈ UJset ε, ∀ x, ‖π g x‖ ≤ C * wt g ^ b * ‖x‖) (hv : ∃ b : ℝ, 0 ≤ b ∧ ∀ b' : ℝ, b ≤ b' → MeasureTheory.Integrable (fun g : UJ ε => wt (uMat g) ^ (-b')) (Formalism.REAL.muG ε).inv), AlmostIsom (UJset ε) π :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Growth.almostIsom_of_growth

theorem iwa_levi : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i), ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ mats (leviOne ε W), ∃ k ∈ maxCpt (mats (leviOne ε W)), ∃ s ∈ mats (leviOne ε W), g = k * s ∧ (Uᴴ * s * U).BlockTriangular id :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi.exists_unitary_iwasawa_leviOne

theorem admissible_of_iwasawa_decomposition : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hI : ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ g ∈ G, ∃ k ∈ maxCpt G, ∃ s ∈ G, g = k * s ∧ (Uᴴ * s * U).BlockTriangular id) (hU : IsURepOn G π) (hirr : IsIrredOn G π), IsAdmOn G π :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.admitted.isAdmOn_of_iwasawa

theorem smooth_deriv : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G), HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) 0 ∧ IsSmoothVec G π (dRep π X v) :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec

theorem smooth_lin : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u v : H} (hu : IsSmoothVec G π u) (hv : IsSmoothVec G π v) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (hY : Y ∈ HCSS.lieOf G), dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π X (u + v) = dRep π X u + dRep π X v ∧ ∀ c : ℂ, dRep π X (c • v) = c • dRep π X v :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear

theorem inv_basis : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} (hG : IsLinRed G), ∃ (d : ℕ) (b : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, b i ∈ HCSS.lieOf G) ∧ LinearIndependent ℝ b ∧ (∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) ∧ ∀ k ∈ maxCpt G, ∃ O : Matrix (Fin d) (Fin d) ℝ, Oᵀ * O = 1 ∧ ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.exists_basis_lieOf_orthogonal

theorem delta_comm : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ G) (O : Matrix (Fin d) (Fin d) ℝ) (hO : Oᵀ * O = 1) (hkb : ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l) {v : H} (hv : IsSmoothVec G π v), π k (∑ i, dRep π (b i) (dRep π (b i) v)) = ∑ i, dRep π (b i) (dRep π (b i) (π k v)) :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.sumSquares_comm

theorem word_of_delta : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) (hQ : AlmostIsom G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hli : LinearIndependent ℝ b) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (hYs : ∀ y ∈ Y, IsSmoothVec G π y) (hYd : ∀ y ∈ Y, ∑ i, dRep π (b i) (dRep π (b i) y) ∈ Y), ∀ v ∈ Y, WordBound G π v :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta.word_bound_of_delta

theorem analytic_uj : ∀ {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hrep : Formalism.QuantumDeterminants.IsCRepOn (UJset ε) π) (hc : ∀ v, ContinuousOn (fun g => π g v) (UJset ε)) {v : H} (hs : IsSmoothVec (UJset ε) π v) (hw : WordBound (UJset ε) π v) (w : H), GlobalTheory.Published.AnalyticOnUJ ε fun g => ⟪w, π g v⟫_ℂ :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.AnalyticWords.analyticOnUJ_of_wordBound

theorem one_param : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hU : IsURepOn G π) {v : H} (hs : IsSmoothVec G π v) (hw : WordBound G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (w : H), AnalyticOnNhd ℝ (fun t : ℝ => ⟪w, π (NormedSpace.exp (t • X)) v⟫_ℂ) Set.univ :=
  @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam.analytic_coeff

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem smooth_word_of_adm {G : Set (Matrix (Fin n) (Fin n) ℂ)} [CompleteSpace H]
    {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hcl : IsClosed G) (hA : IsAdmOn G π) (hQ : AlmostIsom G π) {v : H}
    (hv : IsKFinOn G π v) : IsSmoothVec G π v ∧ WordBound G π v := by
  obtain ⟨hrep, hc, hK, -⟩ := id hA
  obtain ⟨Y, hYf, hvY, hYK, hD⟩ := isotypic hG hA hv
  have hYs : ∀ y ∈ Y, IsSmoothVec G π y := garding hG hcl hrep hc hK Y fun T hT y hy => by
    have := hD ((T : H →ₗ[ℂ] H).comp Y.subtype) (fun k hk y y' e => by
      show T (y' : H) = π k (T (y : H))
      rw [e, hT k hk]) ⟨y, hy⟩
    exact this
  obtain ⟨d, b, hb, hli, hsp, hinv⟩ := inv_basis hG
  refine ⟨hYs v hvY, word_of_delta hG hrep hc hQ b hb hli hsp Y hYs ?_ v hvY⟩
  have hsm : ∀ (y : H), IsSmoothVec G π y → ∀ i, IsSmoothVec G π (dRep π (b i) (dRep π (b i) y)) := fun y hy i =>
    (smooth_deriv hG hrep (smooth_deriv hG hrep hy (hb i)).2 (hb i)).2
  let Dl : Y →ₗ[ℂ] H :=
    { toFun := fun y => ∑ i, dRep π (b i) (dRep π (b i) (y : H))
      map_add' := fun x y => by
        refine Finset.sum_congr rfl (fun i _ => ?_) |>.trans Finset.sum_add_distrib
        have hx := hYs x x.2
        have hy := hYs y y.2
        rw [Submodule.coe_add, (smooth_lin hG hrep hx hy (hb i) (hb i)).2.1,
          (smooth_lin hG hrep (smooth_deriv hG hrep hx (hb i)).2 (smooth_deriv hG hrep hy (hb i)).2
            (hb i) (hb i)).2.1]
      map_smul' := fun c x => by
        have hx := hYs x x.2
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, (smooth_lin hG hrep hx hx (hb i) (hb i)).2.2,
          (smooth_lin hG hrep (smooth_deriv hG hrep hx (hb i)).2 (smooth_deriv hG hrep hx (hb i)).2
            (hb i) (hb i)).2.2] }
  intro y hy
  refine hD Dl (fun k hk y y' e => ?_) ⟨y, hy⟩
  obtain ⟨O, hO, hkb⟩ := hinv k hk
  show ∑ i, dRep π (b i) (dRep π (b i) (y' : H)) = π k (∑ i, dRep π (b i) (dRep π (b i) (y : H)))
  rw [e, delta_comm hG hrep b hb hk.1 O hO hkb (hYs y y.2)]

theorem isClosed_UJset (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  show IsClosed {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem almostIsom_of_unitary {G : Set (Matrix (Fin n) (Fin n) ℂ)} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hU : IsURepOn G π) : AlmostIsom G π := by
  refine ⟨fun x y => ⟪x, y⟫_ℂ, 1, 1, 0, one_pos, zero_le_one, le_refl _, fun x y z => inner_add_right x y z,
    fun c x y => inner_smul_right x y c, fun x y => (inner_conj_symm y x).symm, fun x => ?_, fun x y => ?_,
    fun X hX t x => ?_⟩
  · show 1 * ‖x‖ ^ 2 ≤ (⟪x, x⟫_ℂ).re
    rw [one_mul, inner_self_eq_norm_sq_to_K]; norm_cast
  · show ‖⟪x, y⟫_ℂ‖ ≤ 1 * ‖x‖ * ‖y‖
    rw [one_mul]; exact norm_inner_le_norm x y
  · have h : ∀ u : H, (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := fun u => by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    show (⟪π _ x, π _ x⟫_ℂ).re ≤ _ * (⟪x, x⟫_ℂ).re
    simp only [h, hU.2.1 _ (hX t) x]
    simp

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

namespace GlobalTheory.CompanionTheory.Hypotheses₂

open HCA

theorem admissibleCoefficientsAnalytic : GlobalTheory.Published.AdmissibleCoefficientsAnalytic := by
  intro n ε H _ _ _ π hπ v w hv _
  have hG := GlobalTheory.HCUnitary.isLinRed_UJset ε
  have hA : IsAdmOn (UJset ε) π := GlobalTheory.HCUnitary.isAdmOn_iff.2 hπ
  have hQ : AlmostIsom (UJset ε) π :=
    almost_of_growth hπ.1 hπ.2.1 (growth hπ.1 hπ.2.1 hπ.2.2.1) (volume ε)
  have hv' : IsKFinOn (UJset ε) π v := by
    obtain ⟨S, h1, h2, h3⟩ := hv
    exact ⟨S, h1, h2, GlobalTheory.HCUnitary.isKStable_iff.2 h3⟩
  obtain ⟨hs, hw⟩ := smooth_word_of_adm hG (isClosed_UJset ε) hA hQ hv'
  exact analytic_uj hπ.1 hπ.2.1 hs hw w

theorem leviSubmoduleDense : GlobalTheory.Published.LeviSubmoduleDense := by
  intro n ε a j W hW hj V _ _ _ σ hU hI S hS hK hL
  obtain ⟨hG, hexp⟩ := GlobalTheory.LeviPolar.isLinRed_leviOne n ε a j W hW hj
  have hA : IsAdmOn (mats (leviOne ε W)) σ := admissible_of_iwasawa_decomposition hG (iwa_levi hW hj) hU hI
  have hQ := almostIsom_of_unitary hU
  have hcl : IsClosed (mats (leviOne ε W)) := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isClosedMap _ (isClosed_leviOne hW hj)
  have keep : ∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) →
      ∀ v ∈ S.topologicalClosure, σ (NormedSpace.exp X) v ∈ S.topologicalClosure := fun X hX => by
    have := GlobalTheory.LeviDense.oneParameter_mem_closure (T := fun t : ℝ => σ (NormedSpace.exp (t • X))) (by simp [hU.1.1])
      (fun s t => by
        rw [← hU.1.2 _ (hX s) _ (hX t), add_smul,
          Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)])
      (hL X hX)
      (fun v hv w => by
        obtain ⟨h1, h2⟩ := smooth_word_of_adm hG hcl hA hQ (GlobalTheory.LeviDense.isKFinOn_of_isKFinIn (hK v hv))
        exact one_param hG hU h1 h2 hX w) 1
    simpa only [one_smul] using this
  rcases hI S.topologicalClosure S.isClosed_topologicalClosure (fun g hg v hv => by
    obtain ⟨X, Y, hX, hY, rfl⟩ := hexp g hg
    rw [hU.1.2 _ (by simpa using hX 1) _ (by simpa using hY 1)]
    exact keep X hX _ (keep Y hY v hv)) with h | h
  · exact absurd (le_bot_iff.1 (h ▸ S.le_topologicalClosure)) hS
  · exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

theorem harishChandra_analyticity_density : GlobalTheory.Published.HarishChandraAnalyticity :=
  ⟨admissibleCoefficientsAnalytic, leviSubmoduleDense⟩

end GlobalTheory.CompanionTheory.Hypotheses₂

end
end
