import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCycOInvPow
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SenWeights
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries

section
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory

theorem actTw_eq_twCoef_and_isCoc_iff : ∀ {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]
    (χ : G →* Oˣ),
    (∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m) ∧
    ∀ z : G → ↥L.T ⊗[O] X, tableLineDegreeTwo.IsCoc L X χ z ↔ z ∈ Z1 (twCoef (latRep L) χ X) ⊤ := by
  intro G _ _ LL _ O _ _ V _ _ _ _ ρ L X _ _ χ
  have h1 : ∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m := by
    intro g m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul]
      rw [coefRep_tmul, twistRep_apply]
      simp [latRep, smul_tmul', MonoidHom.inv_apply]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  refine ⟨h1, fun z => ?_⟩
  constructor
  · rintro ⟨hz, hc⟩
    refine ⟨⟨hz, fun _ => Submodule.mem_top⟩, ?_⟩
    show (ReciprocityTheory.Def.d1 (twCoef (latRep L) χ X)) z = 0
    funext x
    change twCoef (latRep L) χ X x.1 (z x.2) - z (x.1 * x.2) + z x.1 = 0
    rw [hc, ← h1]; abel
  · rintro ⟨⟨hz, -⟩, hk⟩
    refine ⟨hz, fun g h => ?_⟩
    have e : twCoef (latRep L) χ X g (z h) - z (g * h) + z g = 0 := congrFun hk (g, h)
    rw [h1, ← sub_eq_zero, ← neg_eq_zero, ← e]; abel

end GlobalTheory
end

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff : ∀ {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]
    (χ : G →* Oˣ),
    (∀ g m, tableLineDegreeTwo.actTw L X χ g m = twCoef (latRep L) χ X g m) ∧
    ∀ z : G → ↥L.T ⊗[O] X, tableLineDegreeTwo.IsCoc L X χ z ↔ z ∈ Z1 (twCoef (latRep L) χ X) ⊤ := by
  atlas_forward_decl GlobalTheory.actTw_eq_twCoef_and_isCoc_iff
end

section
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory

theorem finite_module_killed_by_pow_of_not_isUnit :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (lam : O), ¬ IsUnit lam →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], ∃ a : ℕ, ∀ x : X, lam ^ a • x = 0 := by
  intro O _ _ lam hlam X _ _ _
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes (R := O) X lam
  set Y : Submodule O X := LinearMap.range (lam ^ n • (LinearMap.id : X →ₗ[O] X)) with hY
  have hFG : Y.FG := Module.Finite.iff_fg.mp inferInstance
  have hle : Y ≤ Ideal.span {lam} • Y := by
    intro y hy
    have hy' : y ∈ LinearMap.range (lam ^ (n + 1) • (LinearMap.id : X →ₗ[O] X)) := by
      rw [← hn (n + 1) (Nat.le_succ n)]; exact hy
    obtain ⟨x, rfl⟩ := hy'
    have hmem : lam ^ n • x ∈ Y := ⟨x, by simp⟩
    have : (lam ^ (n + 1) • (LinearMap.id : X →ₗ[O] X)) x = lam • (lam ^ n • x) := by
      simp [pow_succ', mul_smul]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self lam) hmem
  have hjac : Ideal.span {lam} ≤ (⊥ : Ideal O).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal lam).mpr hlam
  have hbot : Y = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ Y hFG hle hjac
  refine ⟨n, fun x => ?_⟩
  have : lam ^ n • x ∈ Y := ⟨x, by simp⟩
  rw [hbot] at this
  simpa using this

end GlobalTheory
end

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_zero_of_finite_of_not_isUnit : ∀ (O : Type) [CommRing O] [IsLocalRing O] (lam : O), ¬ IsUnit lam →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], ∃ a : ℕ, ∀ x : X, lam ^ a • x = 0 := by
  atlas_forward_decl GlobalTheory.finite_module_killed_by_pow_of_not_isUnit
end

section
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

theorem GlobalTheory.admissible_eventually_iff_mem_cls : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) {M : Type} [AddCommGroup M]
    [Module S.O M] (W : Representation S.O S.G M) (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    (∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0) →
    (∀ (a : ℕ) (ha : ∀ x : X, S.Γ.lam ^ a • x = 0), 1 ≤ a →
      S.cls W X = admAt (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut W X a ha) →
    ∀ z : ↥(Z1 (twCoef W S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea W S.Γ.χ₁ ha z)) ↔
        Submodule.Quotient.mk z ∈ S.cls W X) := by
  intro l _ P S M _ _ W X _ _ _ hX hlev z
  constructor
  · rintro ⟨a₀, h⟩
    obtain ⟨a₁, h1⟩ := hX
    have hle1 : a₁ ≤ max a₀ (max a₁ 1) := le_trans (le_max_left _ _) (le_max_right _ _)
    have ha : ∀ x : X, S.Γ.lam ^ (max a₀ (max a₁ 1)) • x = 0 := by
      intro x
      rw [← Nat.sub_add_cancel hle1, pow_add, mul_smul, h1, smul_zero]
    have hA := h (max a₀ (max a₁ 1)) (le_max_left _ _) ha
    have hone : 1 ≤ max a₀ (max a₁ 1) := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [hlev _ ha hone]
    exact (mk_mem_admissibleAt_iff_cocycle ha z).mpr hA
  · intro h
    refine ⟨1, fun a ha1 ha => ?_⟩
    rw [hlev a ha ha1] at h
    exact (mk_mem_admissibleAt_iff_cocycle ha z).mp h
end

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_class_admissible : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) {M : Type} [AddCommGroup M]
    [Module S.O M] (W : Representation S.O S.G M) (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    (∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0) →
    (∀ (a : ℕ) (ha : ∀ x : X, S.Γ.lam ^ a • x = 0), 1 ≤ a →
      S.cls W X = admAt (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut W X a ha) →
    ∀ z : ↥(Z1 (twCoef W S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea W S.Γ.χ₁ ha z)) ↔
        Submodule.Quotient.mk z ∈ S.cls W X) := by
  atlas_forward_decl GlobalTheory.admissible_eventually_iff_mem_cls
end

section
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.AdmQuotExt

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]

def redExt (c : O) : ((↥L.T ⊗[O] X) × O) →ₗ[O] ((↥L.T ⊗[O] X) × (O ⧸ Ideal.span {c})) :=
  LinearMap.prodMap LinearMap.id (Ideal.span {c}).mkQ

omit [TopologicalSpace G] in
theorem redExt_surjective (c : O) : Function.Surjective (redExt L X c) := by
  rintro ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  exact ⟨(m, y), rfl⟩

omit [TopologicalSpace G] in
theorem ker_redExt (lam : O) (a : ℕ) : LinearMap.ker (redExt L X (lam ^ a)) = tableLineDegreeTwo.kerExt L X lam a := by
  rw [redExt, LinearMap.ker_prodMap, LinearMap.ker_id, Submodule.ker_mkQ]
  rfl

theorem redExt_actExt (χ₁ : G →* Oˣ) {c : O} (hc : ∀ x : X, c • x = 0)
    (z : G → ↥L.T ⊗[O] X) (hz : z ∈ Z1 (twCoef (latRep L) χ₁ X) ⊤) (g : G) (x : (↥L.T ⊗[O] X) × O) :
    redExt L X c (tableLineDegreeTwo.actExt L X χ₁ z g x) = Ea (latRep L) χ₁ hc ⟨z, hz⟩ g (redExt L X c x) := by
  obtain ⟨m, y⟩ := x
  have h := Ea_apply (latRep L) χ₁ hc ⟨z, hz⟩ g m y
  change (_, _) = Ea (latRep L) χ₁ hc ⟨z, hz⟩ g (m, Ideal.Quotient.mk _ y)
  rw [h]
  simp only [tableLineDegreeTwo.actExt, smul_smul, mul_comm y]
  rfl

end Gen

set_option maxHeartbeats 2000000 in

theorem admissible_quotientExtension_iff_admissible_ext' : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ),
    (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) →
    ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T.ρ) (X : Type) [AddCommGroup X] [Module S.O X]
      (z : S.G → ↥L.T ⊗[S.O] X) (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤) (a : ℕ)
      (ha : ∀ x : X, S.Γ.lam ^ a • x = 0),
      (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
                         (tableLineDegreeTwo.kerExt L X S.Γ.lam a) ↔ S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩)) := by
  intro l _ P S jT hj T L X _ _ z hz a ha
  have h := GlobalTheory.FullCharpoly.admissibleQuotient_iff_admissible_module S jT hj _ _ (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
    (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩) (redExt L X (S.Γ.lam ^ a)) (redExt_surjective L X _)
    (redExt_actExt L X S.Γ.χ₁ ha z hz)
  rw [ker_redExt L X S.Γ.lam a] at h
  exact h

end GlobalTheory.AdmQuotExt
end

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_quotientExtension_iff_admissible_ext : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ),
    (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) →
    ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T.ρ) (X : Type) [AddCommGroup X] [Module S.O X]
      (z : S.G → ↥L.T ⊗[S.O] X) (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤) (a : ℕ)
      (ha : ∀ x : X, S.Γ.lam ^ a • x = 0),
      (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
                         (tableLineDegreeTwo.kerExt L X S.Γ.lam a) ↔ S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩)) := by
  atlas_forward_decl GlobalTheory.AdmQuotExt.admissible_quotientExtension_iff_admissible_ext'
end

section
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.TransportCoef

open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (d0 d1 C1)

variable {O G : Type} [CommRing O] [Group G] {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M']
  [Module O M']

theorem rTensor_coefRep (W : Representation O G M) (W' : Representation O G M') (e : M →ₗ[O] M')
    (he : ∀ g x, e (W g x) = W' g (e x)) (X : Type) [AddCommGroup X] [Module O X] (g : G) (y : M ⊗[O] X) :
    LinearMap.rTensor X e (coefRep W X g y) = coefRep W' X g (LinearMap.rTensor X e y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m x => rw [coefRep_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, coefRep_tmul, he]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem twist_intertwine (W : Representation O G M) (W' : Representation O G M') (e : M →ₗ[O] M')
    (he : ∀ g x, e (W g x) = W' g (e x)) (χ : G →* Oˣ) (g : G) (x : M) :
    e (twistRep W χ g x) = twistRep W' χ g (e x) := by
  rw [twistRep_apply, twistRep_apply, map_smul, he]

variable [TopologicalSpace G]

section General

variable {P P' : Type} [AddCommGroup P] [Module O P] [AddCommGroup P'] [Module O P']
  (π : Representation O G P) (π' : Representation O G P') (F : P →ₗ[O] P')
  (hF : ∀ g y, F (π g y) = π' g (F y))
include hF

theorem mem_Z1_comp {z : G → P} (hz : z ∈ Z1 π ⊤) : (fun g => F (z g)) ∈ Z1 π' ⊤ := by
  rw [Z1, Submodule.mem_inf] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  refine ⟨⟨h1.1.comp F, fun _ => Submodule.mem_top⟩, ?_⟩
  rw [LinearMap.mem_ker] at h2 ⊢
  funext x
  have := congrFun h2 x
  simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this ⊢
  rw [← hF, ← map_sub, ← map_add, this, map_zero]

theorem cob_comp {z : G → P} (S : Set G) (b : P) (hb : ∀ g ∈ S, z g = π g b - b) :
    ∀ g ∈ S, F (z g) = π' g (F b) - F b := by
  intro g hg
  rw [hb g hg, map_sub, hF]

theorem mem_B1_comp {z : G → P} (hz : z ∈ B1 π ⊤) : (fun g => F (z g)) ∈ B1 π' ⊤ := by
  rw [ReciprocityTheory.Def.B1, Submodule.mem_map] at hz ⊢
  obtain ⟨b, -, rfl⟩ := hz
  refine ⟨F b, Submodule.mem_top, ?_⟩
  funext g
  simp only [d0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_sub, hF]

end General

end GlobalTheory.TransportCoef

namespace GlobalTheory.TransportCoef
open Formalism.MainNotions.N (twistRep coefRep)

theorem transport {O G : Type} [CommRing O] [Group G] [TopologicalSpace G] {M M' : Type} [AddCommGroup M]
    [Module O M] [AddCommGroup M'] [Module O M'] (W : Representation O G M) (W' : Representation O G M')
    (e : M ≃ₗ[O] M') (he : ∀ g x, e (W g x) = W' g (e x)) :
    ∀ (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X),
      (∀ g, z' g = LinearEquiv.rTensor X e (z g)) →
      (z ∈ Z1 (twCoef W χ X) ⊤ ↔ z' ∈ Z1 (twCoef W' χ X) ⊤) ∧
      (∀ (hz : z ∈ Z1 (twCoef W χ X) ⊤) (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0),
        ∃ f : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] ((M' ⊗[O] X) × (O ⧸ Ideal.span {c})),
          ∀ g x, f (Ea W χ hc ⟨z, hz⟩ g x) = Ea W' χ hc ⟨z', hz'⟩ g (f x)) ∧
      (z ∈ B1 (twCoef W χ X) ⊤ ↔ z' ∈ B1 (twCoef W' χ X) ⊤) ∧
      ∀ I : Subgroup G, (∃ b, ∀ g ∈ I, z g = twCoef W χ X g b - b) ↔
        (∃ b', ∀ g ∈ I, z' g = twCoef W' χ X g b' - b') := by
  intro χ X _ _ z z' hzz
  have he' : ∀ g x, e.symm (W' g x) = W g (e.symm x) := fun g x => by
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let E := LinearEquiv.rTensor X e
  have hE : ∀ y, E y = LinearMap.rTensor X (e : M →ₗ[O] M') y := fun _ => rfl
  have hEs : ∀ y, E.symm y = LinearMap.rTensor X (e.symm : M' →ₗ[O] M) y := by
    intro y
    apply E.injective
    rw [LinearEquiv.apply_symm_apply, hE, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    simp
  have key : ∀ g y, (E : M ⊗[O] X →ₗ[O] M' ⊗[O] X) (twCoef W χ X g y) = twCoef W' χ X g (E y) := fun g y =>
    rTensor_coefRep (twistRep W χ⁻¹) (twistRep W' χ⁻¹) (e : M →ₗ[O] M')
      (twist_intertwine W W' (e : M →ₗ[O] M') he χ⁻¹) X g y
  have keys : ∀ g y, (E.symm : M' ⊗[O] X →ₗ[O] M ⊗[O] X) (twCoef W' χ X g y) = twCoef W χ X g (E.symm y) :=
    fun g y => by
      show E.symm _ = _
      rw [hEs, hEs]
      exact rTensor_coefRep (twistRep W' χ⁻¹) (twistRep W χ⁻¹) (e.symm : M' →ₗ[O] M)
        (twist_intertwine W' W (e.symm : M' →ₗ[O] M) he' χ⁻¹) X g y
  have keyc : ∀ g y, E (coefRep W X g y) = coefRep W' X g (E y) := fun g y =>
    rTensor_coefRep W W' (e : M →ₗ[O] M') he X g y
  have hz'f : z' = fun g => (E : M ⊗[O] X →ₗ[O] M' ⊗[O] X) (z g) := funext hzz
  have hzf : z = fun g => (E.symm : M' ⊗[O] X →ₗ[O] M ⊗[O] X) (z' g) := by
    funext g; show z g = E.symm (z' g); rw [hzz, LinearEquiv.symm_apply_apply]
  refine ⟨⟨fun hz => ?_, fun hz' => ?_⟩, ?_, ⟨fun hz => ?_, fun hz' => ?_⟩, fun I => ⟨?_, ?_⟩⟩
  · rw [hz'f]; exact mem_Z1_comp _ _ _ key hz
  · rw [hzf]; exact mem_Z1_comp _ _ _ keys hz'
  · intro hz hz' c hc
    refine ⟨E.prodCongr (LinearEquiv.refl O _), fun g x => ?_⟩
    obtain ⟨m, q⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [LinearEquiv.prodCongr_apply, Ea_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.refl_apply, Ea_apply]
    simp only [Prod.mk.injEq, and_true]
    rw [map_add, map_smul, keyc, hzz]
  · rw [hz'f]; exact mem_B1_comp _ _ _ key hz
  · rw [hzf]; exact mem_B1_comp _ _ _ keys hz'
  · rintro ⟨b, hb⟩
    refine ⟨E b, fun g hg => ?_⟩
    rw [hzz]
    exact cob_comp _ _ _ key (I : Set G) b hb g hg
  · rintro ⟨b, hb⟩
    refine ⟨E.symm b, fun g hg => ?_⟩
    rw [hzf]
    exact cob_comp _ _ _ keys (I : Set G) b hb g hg

end GlobalTheory.TransportCoef
end

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariantIso_transport_cocycles_extensions : ∀ {O G : Type} [CommRing O] [Group G] [TopologicalSpace G] {M M' : Type} [AddCommGroup M]
    [Module O M] [AddCommGroup M'] [Module O M'] (W : Representation O G M) (W' : Representation O G M')
    (e : M ≃ₗ[O] M'), (∀ g x, e (W g x) = W' g (e x)) →
    ∀ (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X),
      (∀ g, z' g = LinearEquiv.rTensor X e (z g)) →
      (z ∈ Z1 (twCoef W χ X) ⊤ ↔ z' ∈ Z1 (twCoef W' χ X) ⊤) ∧
      (∀ (hz : z ∈ Z1 (twCoef W χ X) ⊤) (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0),
        ∃ f : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] ((M' ⊗[O] X) × (O ⧸ Ideal.span {c})),
          ∀ g x, f (Ea W χ hc ⟨z, hz⟩ g x) = Ea W' χ hc ⟨z', hz'⟩ g (f x)) ∧
      (z ∈ B1 (twCoef W χ X) ⊤ ↔ z' ∈ B1 (twCoef W' χ X) ⊤) ∧
      ∀ I : Subgroup G, (∃ b, ∀ g ∈ I, z g = twCoef W χ X g b - b) ↔
        (∃ b', ∀ g ∈ I, z' g = twCoef W' χ X g b' - b') := by
  atlas_forward_decl GlobalTheory.TransportCoef.transport
end

section
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.CharLat

theorem nonempty_equiv_of_free {O K : Type} [CommRing O] [IsDomain O] [Field K] [Module O K]
    (φ : O →+* K) (hsm : ∀ (o : O) (x : K), o • x = φ o * x)
    (hfr : ∀ z : K, ∃ a d : O, d ≠ 0 ∧ z * φ d = φ a)
    (T : Submodule O K) [Module.Free O T] (hT : T ≠ ⊥) :
    Nonempty (O ≃ₗ[O] T) := by
  let b := Module.Free.chooseBasis O T
  haveI hsub : Subsingleton (Module.Free.ChooseBasisIndex O T) := by
    constructor
    intro i j
    by_contra hij
    have hi : ((b i : T) : K) ≠ 0 := fun h0 => b.ne_zero i (Subtype.ext h0)
    obtain ⟨a, d, hd0, hd⟩ := hfr (((b j : T) : K) / ((b i : T) : K))
    have hrel : d • b j + (-a) • b i = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm, ZeroMemClass.coe_zero,
        map_neg, ← hd]
      field_simp
      ring
    have hinj : Function.Injective ![j, i] := by
      intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · exact absurd (hxy : j = i).symm hij
      · exact absurd (hxy : i = j) hij
      · rfl
    have hli : LinearIndependent O ![b j, b i] := by
      have := b.linearIndependent.comp ![j, i] hinj
      convert this using 1
      ext k
      fin_cases k <;> rfl
    have h2 := LinearIndependent.pair_iff.1 hli d (-a) hrel
    exact hd0 h2.1
  haveI hne : Nonempty (Module.Free.ChooseBasisIndex O T) := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hT
    rw [eq_bot_iff]
    intro x hx
    have h0 : (⟨x, hx⟩ : T) = 0 := b.repr.injective (Subsingleton.elim _ _)
    simpa using congrArg Subtype.val h0
  haveI : Unique (Module.Free.ChooseBasisIndex O T) := uniqueOfSubsingleton (Classical.arbitrary _)
  exact ⟨(LinearEquiv.funUnique (Module.Free.ChooseBasisIndex O T) O O).symm.trans b.equivFun.symm⟩

end GlobalTheory.CharLat

namespace GlobalTheory.CharLat

set_option maxHeartbeats 2000000 in

theorem exists_equiv_charLattice : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) {G : Type} [Group G] [TopologicalSpace G]
    (θ : G →* (↥(OL LL))ˣ) (Lc : Lattice (O := ↥(OL LL)) (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) θ))),
    ∃ e : ↥(OL LL) ≃ₗ[↥(OL LL)] ↥Lc.T, ∀ g a, e (Formalism.GaloisCohomology.scalRep (↥(OL LL)) θ g a) = latRep Lc g (e a) := by
  intro l _ LL G _ _ θ Lc
  haveI := LL.2
  haveI hF : IsFractionRing (↥(OL LL)) (↥LL.1) :=
    integralClosure.isFractionRing_of_finite_extension (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥LL.1)
  haveI := Lc.free
  have hT : Lc.T ≠ ⊥ := by
    intro h
    have hs := Lc.span
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at hs
    exact bot_ne_top hs
  have hsm : ∀ (o : ↥(OL LL)) (x : ↥LL.1), o • x = algebraMap (↥(OL LL)) (↥LL.1) o * x :=
    fun o x => rfl
  have hfr : ∀ z : ↥LL.1, ∃ a d : ↥(OL LL), d ≠ 0 ∧ z * algebraMap (↥(OL LL)) (↥LL.1) d =
      algebraMap (↥(OL LL)) (↥LL.1) a := by
    intro z
    obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (↥(OL LL))) z
    exact ⟨a, d, nonZeroDivisors.coe_ne_zero d, hd⟩
  obtain ⟨e⟩ := nonempty_equiv_of_free (algebraMap (↥(OL LL)) (↥LL.1)) hsm hfr Lc.T hT
  refine ⟨e, fun g a => ?_⟩
  rw [Formalism.GaloisCohomology.scalRep_apply, map_smul]
  apply Subtype.ext
  rw [Submodule.coe_smul, hsm]
  rfl

end GlobalTheory.CharLat
end

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_stableLattice_integralCharacter : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) {G : Type} [Group G] [TopologicalSpace G]
    (θ : G →* (↥(OL LL))ˣ) (Lc : Lattice (O := ↥(OL LL)) (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) θ))),
    ∃ e : ↥(OL LL) ≃ₗ[↥(OL LL)] ↥Lc.T, ∀ g a, e (Formalism.GaloisCohomology.scalRep (↥(OL LL)) θ g a) = latRep Lc g (e a) := by
  atlas_forward_decl GlobalTheory.CharLat.exists_equiv_charLattice
end

section
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

open Formalism.MainNotions.N (twistRep coefRep)

namespace GlobalTheory.AdmLoc

theorem mk_mem_H1fX_iff_inHfX {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (ρ' : Representation LL G V) (L' : Lattice (O := O) ρ')
    (X : Type) [AddCommGroup X] [Module O X] (χ : G →* Oˣ) :
    (∀ g, ρ' g = ((tableLineDegreeTwo.charL (LL := LL) χ g)⁻¹ : LLˣ).val • ρ g) → L'.T = L.T →
    ∀ (z : G → ↥L.T ⊗[O] X) (hz : z ∈ Z1 (twCoef (latRep L) χ X) ⊤),
      (Submodule.Quotient.mk ⟨z, hz⟩ ∈ finiteSelmer PD L χ X ↔ tableLineDegreeTwo.InHfX PD L L' X χ z) := by
  intro hρ hT z hz
  have e1 : ρ' = twistRep ρ (chiLL LL χ⁻¹) := by
    ext g v
    rw [hρ g, twistRep_apply]
    simp [chiLL, tableLineDegreeTwo.charL]
  subst e1
  have e2 : L' = twLattice L χ⁻¹ := by
    cases L'
    simp only at hT
    subst hT
    rfl
  subst e2
  have hact : ∀ g (m : ↥L.T ⊗[O] X), twCoef (latRep L) χ X g m = tableLineDegreeTwo.actTw L X χ g m := by
    intro g m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [coefRep_tmul, twistRep_apply]
      simp only [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, smul_tmul']
      rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hA : toAmb (twCoef (latRep L) χ X) (Submodule.Quotient.mk ⟨z, hz⟩) = Submodule.Quotient.mk z := rfl
  rw [finiteSelmer, Submodule.mem_comap, hA, LinearMap.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset u
    have hrep : ∀ p : ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹)), ∃ c : ↥(latticeCocycles (twLattice L χ⁻¹)),
        (c : G → V) ∈ latticeFiniteCocycles PD (twLattice L χ⁻¹) ∧ Submodule.Quotient.mk c = (p : LatticeCohomology (twLattice L χ⁻¹)) := by
      rintro ⟨p, hp⟩
      obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hp
      exact ⟨c, hc, rfl⟩
    choose rep hrepf hrepmk using hrep
    let e := S.equivFin
    let cc : Fin S.card → ↥(latticeCocycles (twLattice L χ⁻¹)) := fun j => rep (e.symm j).1.1
    let xx : Fin S.card → X := fun j => (e.symm j).1.2
    have key : (tensAmb L χ X ∘ₗ (latticeFiniteCohomology PD (twLattice L χ⁻¹)).subtype.rTensor X)
        (∑ p ∈ S, p.1 ⊗ₜ[O] p.2) = Submodule.Quotient.mk (∑ j, tensCoc L χ X (cc j) (xx j)) := by
      rw [map_sum, ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
      refine Eq.trans ?_ (map_sum (Submodule.mkQ _) _ _).symm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply, ← hrepmk, tensAmb_tmul]
      rfl
    rw [key] at hu
    obtain ⟨m, -, hm⟩ := (Submodule.Quotient.eq _).mp hu
    refine ⟨S.card, fun j g => evT (twLattice L χ⁻¹) g (cc j), xx, -m, fun j => hrepf _, fun g => ?_⟩
    have h1 : twCoef (latRep L) χ X g m - m = (∑ j, tensCoc L χ X (cc j) (xx j)) g - z g := congrFun hm g
    simp only [Finset.sum_apply] at h1
    rw [hact] at h1
    simp only [map_neg]
    have h2 : ∀ j, tensCoc L χ X (cc j) (xx j) g = evT (twLattice L χ⁻¹) g (cc j) ⊗ₜ[O] xx j := fun j => rfl
    simp only [h2] at h1
    have h3 : z g = ∑ j, evT (twLattice L χ⁻¹) g (cc j) ⊗ₜ[O] xx j - (tableLineDegreeTwo.actTw L X χ g m - m) := by
      rw [h1]; abel
    rw [h3]
    abel
  · rintro ⟨k, c, x, m, hc, hzc⟩
    let cc : Fin k → ↥(latticeCocycles (twLattice L χ⁻¹)) := fun j => ⟨fun g => (c j g : V), (hc j).1⟩
    refine ⟨∑ j, (⟨Submodule.Quotient.mk (cc j), Submodule.mem_map_of_mem (hc j)⟩ :
      ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹))) ⊗ₜ[O] x j, ?_⟩
    rw [map_sum]
    have h1 : ∀ j, (tensAmb L χ X ∘ₗ (latticeFiniteCohomology PD (twLattice L χ⁻¹)).subtype.rTensor X)
        ((⟨Submodule.Quotient.mk (cc j), Submodule.mem_map_of_mem (hc j)⟩ :
          ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹))) ⊗ₜ[O] x j) = Submodule.mkQ _ (tensCoc L χ X (cc j) (x j)) := fun j => rfl
    simp only [h1]
    rw [← map_sum, Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    refine Submodule.mem_map.mpr ⟨-m, Submodule.mem_top, ?_⟩
    funext g
    change twCoef (latRep L) χ X g (-m) - (-m) = (∑ j, tensCoc L χ X (cc j) (x j)) g - z g
    simp only [Finset.sum_apply, hact, map_neg, hzc g]
    have h2 : ∀ j, tensCoc L χ X (cc j) (x j) g = c j g ⊗ₜ[O] x j := fun j => rfl
    simp only [h2]
    abel

end GlobalTheory.AdmLoc
end

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_data_dual_exact : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (ρ' : Representation LL G V) (L' : Lattice (O := O) ρ')
    (X : Type) [AddCommGroup X] [Module O X] (χ : G →* Oˣ),
    (∀ g, ρ' g = ((tableLineDegreeTwo.charL (LL := LL) χ g)⁻¹ : LLˣ).val • ρ g) → L'.T = L.T →
    ∀ (z : G → ↥L.T ⊗[O] X) (hz : z ∈ Z1 (twCoef (latRep L) χ X) ⊤),
      (Submodule.Quotient.mk ⟨z, hz⟩ ∈ finiteSelmer PD L χ X ↔ tableLineDegreeTwo.InHfX PD L L' X χ z) := by
  atlas_forward_decl GlobalTheory.AdmLoc.mk_mem_H1fX_iff_inHfX
end

section
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.Per.LetterJumps

theorem card_jumps_letter : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (V : Type) [AddCommGroup V] [Module ↥LL.1 V]
      [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
      (ρ : Representation ↥LL.1 ↥(GK K) V) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ),
      IsCrys (P.PD K) ρ →
      (∀ i τ, tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ → ∀ a, multV (P.PD K) ρ τ a = (U i).count a) →
      ∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 V := by
  intro l _ P AI hT H K LL hA V _ _ _ _ _ ρ U hC hU i
  classical
  obtain ⟨T⟩ := hT
  haveI := LL.2
  haveI := (P.PD K).finK
  have e : K0 K = K.1 := inf_eq_left.2 hA.1
  let eK : ↥K.1 ≃ₐ[ℚ_[l]] ↥(K0 K) := IntermediateField.equivOfEq e.symm
  let τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 := ((H.W K 1 LL hA.2.2).emb i).comp eK.toAlgHom
  have hτ : tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ := by
    refine AlgHom.ext fun x => ?_
    show (H.W K 1 LL hA.2.2).emb i (eK (algebraMap ↥(K0 K) ↥K.1 x)) = (H.W K 1 LL hA.2.2).emb i x
    congr 1
  have hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 := by
    rw [← Nat.card_congr ((IntermediateField.equivOfEq e).arrowCongr (AlgEquiv.refl : ↥LL.1 ≃ₐ[ℚ_[l]] ↥LL.1)),
      ← Nat.card_congr (Equiv.ofBijective _ (H.W K 1 LL hA.2.2).emb_bij), Nat.card_zmod]
    exact (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq
  have hdim := (GlobalTheory.Per.LetterDim.tied_letter_component_finrank l P AI T K LL V ρ).2 hc
    (GlobalTheory.TopSteps.CrysRules.isDR T K LL ρ hC) τ
  haveI := (GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ).1
  haveI : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) ρ) inf_le_left
  obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) ρ τ
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) ρ τ
  obtain ⟨b0, hb0⟩ := (U i).toFinset.bddBelow
  obtain ⟨b1, hb1⟩ := (U i).toFinset.bddAbove
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m : ℤ, m ≤ lo ∧ m ≤ b0 ∧ m ≤ hi :=
    ⟨min (min lo b0) hi, by omega, by omega, by omega⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, hi ≤ k ∧ b1 < k := ⟨max hi (b1 + 1), by omega, by omega⟩
  have hmk : m ≤ k := by omega
  have hsum := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV (P.PD K) ρ τ m k hmk
  rw [hlo m hm1, hhi k hk1, finrank_bot, Nat.cast_zero, sub_zero, hdim] at hsum
  have hsub : (U i).toFinset ⊆ Finset.Ico m k := fun a ha => by
    have h0 := hb0 (Finset.mem_coe.2 ha)
    have h1 := hb1 (Finset.mem_coe.2 ha)
    rw [Finset.mem_Ico]
    omega
  have hcnt : ∑ a ∈ Finset.Ico m k, ((U i).count a : ℤ) = (Multiset.card (U i) : ℤ) := by
    rw [← Multiset.toFinset_sum_count_eq, Nat.cast_sum]
    exact (Finset.sum_subset hsub fun a _ ha => by
      rw [Multiset.mem_toFinset] at ha
      rw [Multiset.count_eq_zero.2 ha, Nat.cast_zero]).symm
  have := (Finset.sum_congr rfl fun a _ => hU i τ hτ a).symm.trans hsum
  rw [hcnt] at this
  exact_mod_cast this

end GlobalTheory.Per.LetterJumps
end

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hodgeTate_jumps_crystalline_eq_dim : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (V : Type) [AddCommGroup V] [Module ↥LL.1 V]
      [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
      (ρ : Representation ↥LL.1 ↥(GK K) V) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ),
      IsCrys (P.PD K) ρ →
      (∀ i τ, tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ → ∀ a, multV (P.PD K) ρ τ a = (U i).count a) →
      ∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 V := by
  atlas_forward_decl GlobalTheory.Per.LetterJumps.card_jumps_letter
end

section
noncomputable section

namespace GlobalTheory.SenCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Operators

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D]

def NabOn (π : A) (g : D →ₗ[O] D) (P : Submodule O D) (nb : ↥P →ₗ[O] ↥P) : Prop :=
  ∀ x : ↥P, π • ((nb x : ↥P) : D) = g x - x

variable {π : A} {g : D →ₗ[O] D} {P Q : Submodule O D}

end Operators

section Residue

variable {O : Type} [CommRing O]

end Residue

section Sen

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D] [IsDomain O] [IsDiscreteValuationRing O]

end Sen

section Wach

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem NΔl_eq (i : ZMod n) : DiagonalQuotientEigen.NΔl W T i = SenWeightsAlt.Ni W T i := rfl

theorem γD_smulA (g : W.Gam) (a : LetA O n) (x : W.DD T) : W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rwa [algebraMap_smul, W.γE_ext, algebraMap_smul] at this

theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i) = letE i := by
  funext j
  change W.γ₀ g (Pi.single (M := fun _ => PowerSeries O) i 1 j) = Pi.single (M := fun _ => PowerSeries O) i 1 j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem mul_letE {a b : LetA O n} {i : ZMod n} (h : a i = b i) : a * letE i = b * letE i := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [h]
  · simp [letE, hj]

theorem letE_mul (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  rw [mul_letE (b := 1) (by simp [letE]), one_mul]

theorem mem_Ni {i : ZMod n} {x : W.DD T} :
    x ∈ SenWeightsAlt.Ni W T i ↔ x ∈ W.NΔ T ∧ (letE i : LetA O n) • x = x := by
  refine and_congr_right fun hx => ⟨?_, fun h => ⟨x, hx.1, h⟩⟩
  rintro ⟨y, -, rfl⟩
  change (letE i : LetA O n) • (letE i : LetA O n) • y = (letE i : LetA O n) • y
  rw [smul_smul, letE_mul]

theorem γD_mem_Ni {i : ZMod n} (g : W.Gam) {x : W.DD T} (hx : x ∈ SenWeightsAlt.Ni W T i) :
    W.γD T g x ∈ SenWeightsAlt.Ni W T i := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_Ni W T).1 hx
  refine (mem_Ni W T).2 ⟨⟨W.N_Γ T g x h1, fun δ hδ => ?_⟩, ?_⟩
  · rw [← W.γD_mul, mul_comm, W.γD_mul, h2 δ hδ]
  · rw [← γA_letE W g i, ← γD_smulA, h3]

theorem γA_mem_AΔ (g : W.Gam) {c : LetA O n} (hc : c ∈ W.AΔ) : W.γA g c ∈ W.AΔ := fun δ hδ => by
  funext j
  have h : W.γ₀ δ (c j) = c j := congrFun (hc δ hδ) j
  change (W.γ₀ δ * W.γ₀ g) (c j) = W.γ₀ g (c j)
  rw [← map_mul, mul_comm, map_mul, AlgHom.mul_apply, h]

theorem twγ_one (g : W.Gam) : SenWeightsAlt.twγ W g T 1 = W.γD T g :=
  LinearMap.ext fun x => one_smul (LetA O n) (W.γD T g x)

section RankOne

variable {r : ℕ} (hr : r = 1) (β : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hβ : ∀ k, (β k : W.DD T) ∈ W.NΔ T)
include hr hβ

end RankOne

end Wach

section Prime

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P)

def OpFrom (m : ℤ) : Prop :=
  5 ≤ l → ∀ (K LL : FinExt l) (hA : CaseA K LL) (g : (H.W K 1 LL hA.2.2).Gam),
    (((H.W K 1 LL hA.2.2).χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) = 1 + (l : ↥(OL LL)) →
    ∀ (h : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ)
      (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      CrysWith (P.PD K) (H.W K 1 LL hA.2.2).emb T.ρ U → (∀ i, ∀ u ∈ U i, 0 ≤ u ∧ u ≤ h i) →
      (∀ i, DiagonalQuotientEigen.SenPair (H.W K 1 LL hA.2.2) T g 1 i (U i) 0) ∧
        ∀ (χ₁ : ↥(GK K) →* (↥(OL LL))ˣ) (w : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℤ)
          (hχ : IsCrysChar (LL := ↥LL.1) (P.PD K) (H.W K 1 LL hA.2.2).emb χ₁ w),
          (∀ i, m ≤ w i ∧ w i ≤ h i) →
          ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
            (b : (H.W K 1 LL hA.2.2).DD (charLat ℚ_[l] Subtype.val_injective χ₁ hχ.1))
            (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))),
            DiagonalQuotientEigen.IsGenWith (H.W K 1 LL hA.2.2) (charLat ℚ_[l] Subtype.val_injective χ₁ hχ.1) g i b a →
              DiagonalQuotientEigen.SenPair (H.W K 1 LL hA.2.2) T g a i (U i) (w i)

theorem OpFrom.mono {m m' : ℤ} (hm : m ≤ m') (h : OpFrom P H m) : OpFrom P H m' :=
  fun h5 K LL hA g hg hh U T hT hU => ⟨(h h5 K LL hA g hg hh U T hT hU).1, fun χ₁ w hχ hw =>
    (h h5 K LL hA g hg hh U T hT hU).2 χ₁ w hχ fun i => ⟨hm.trans (hw i).1, (hw i).2⟩⟩

variable {K LL : FinExt l} (hA : CaseA K LL)

theorem standing_iff {hg : Good K 1 LL} (lam : ↥(OL LL)) :
    Standing P K LL (H.W K 1 LL hg).emb lam ↔ 5 ≤ l ∧ CaseA K LL ∧ Irreducible lam :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.2.2.2⟩, fun h => ⟨h.1, h.2.1, by rw [show K0 K = K.1 from inf_eq_left.2 h.2.1.1],
    (H.W K 1 LL hg).emb_bij, (H.W K 1 LL hg).emb_σ, h.2.2⟩⟩

end Prime

end GlobalTheory.SenCompare
end
end

section
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.TopWindow

theorem exists_topData_galData : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l)
    (hA : CaseA K LL) (lam : ↥(OL LL)), Irreducible lam → 5 ≤ (P.PD K).p →
    ∀ (t : ℕ) (h w η : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) (typ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool)
      (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
      (χ : ℕ → ↥(GK K) →* (↥(OL LL))ˣ), tableLineDegreeTwo.TopHyp (P.PD K) (H.W K 1 LL hA.2.2).emb t h w η typ U T.ρ χ →
      (∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 T.V) →
      ∃ (r : ℕ) (D : TopData (Module.finrank ℚ_[l] ↥(K0 K)) r) (ε : ↥(GK K) →* (↥(OL LL))ˣ),
        GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Hyp P K LL (H.W K 1 LL hA.2.2).emb D
          (GalData.mk lam T (χ 1) ε) ∧ D.t = t ∧
        (∀ i a, ((D.Ut i).count a : ℤ) = tableLineDegreeTwo.jTil U w t i a) ∧
        ∀ c ∈ Finset.Icc 1 t,
          (GalData.mk lam T (χ 1) ε : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)).chi c = χ c := by
  intro l _ P H K LL hA lam hlam h5 t h w η typ U T χ hyp hc
  have hp : (P.PD K).p = l := P.PD_p K
  have hS : Standing P K LL (H.W K 1 LL hA.2.2).emb lam :=
    (GlobalTheory.SenCompare.standing_iff P H lam).2 ⟨hp ▸ h5, hA, hlam⟩
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hS⟩
  obtain ⟨ht, hposition, -, hcrys, hmult, hchi⟩ := hyp
  rw [hp] at hposition
  obtain ⟨D, hDt, hD, t1, t2, t3⟩ := GlobalTheory.TopWindow.exists_topData_of_positionHyps l _ t _ h w η typ U
    (Fact.out : l.Prime).two_le ht hc hposition
  obtain ⟨-, hcont1, hcrys1, hjump1⟩ := hchi 1 (Finset.mem_Icc.2 ⟨le_rfl, ht⟩)
  have hcyc : ∀ g, tableLineDegreeTwo.charL (LL := ↥LL.1) (GlobalTheory.AdmLoc.CycWitness.cycO P K LL) g =
      Formalism.MainNotions.N.cycLL (P.PD K) ↥LL.1 g := fun g => Units.ext (GlobalTheory.AdmLoc.CycWitness.cycO_val P K LL g)
  refine ⟨_, D, GlobalTheory.AdmLoc.CycWitness.cycO P K LL,
    ⟨hS, ⟨rfl, ⟨hcrys, fun i τ hτ a => ?_⟩, ⟨hcont1, hcrys1, fun i τ hτ a => ?_⟩,
      GlobalTheory.AdmLoc.CycWitness.cycO_val P K LL⟩, t1, t2, t3⟩, hDt, fun i a => (hD i).2.2 a, fun c hc' => ?_⟩
  · rw [(hD i).2.1]
    exact hmult i τ (AlgHom.ext fun x => hτ x) a
  · refine (hjump1 i τ (AlgHom.ext fun x => hτ x) a).trans ?_
    show _ = ((Multiset.count a {D.w i} : ℕ) : ℤ)
    rw [(hD i).1, Multiset.count_singleton]
    push_cast
    simp only [add_sub_cancel_right]
  · obtain ⟨hχc, -⟩ := hchi c hc'
    refine MonoidHom.ext fun g => ?_
    apply Units.map_injective (f := (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom) Subtype.val_injective
    change tableLineDegreeTwo.charL (LL := ↥LL.1) (χ 1 * GlobalTheory.AdmLoc.CycWitness.cycO P K LL ^ (-((c : ℤ) - 1))) g =
      tableLineDegreeTwo.charL (LL := ↥LL.1) (χ c) g
    rw [hχc g, ← hcyc g]
    simp [tableLineDegreeTwo.charL, map_zpow]

end GlobalTheory.TopWindow
end

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numerical_galoisData_localSituation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l)
    (hA : CaseA K LL) (lam : ↥(OL LL)), Irreducible lam → 5 ≤ (P.PD K).p →
    ∀ (t : ℕ) (h w η : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) (typ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool)
      (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
      (χ : ℕ → ↥(GK K) →* (↥(OL LL))ˣ), tableLineDegreeTwo.TopHyp (P.PD K) (H.W K 1 LL hA.2.2).emb t h w η typ U T.ρ χ →
      (∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 T.V) →
      ∃ (r : ℕ) (D : TopData (Module.finrank ℚ_[l] ↥(K0 K)) r) (ε : ↥(GK K) →* (↥(OL LL))ˣ),
        GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Hyp P K LL (H.W K 1 LL hA.2.2).emb D
          (GalData.mk lam T (χ 1) ε) ∧ D.t = t ∧
        (∀ i a, ((D.Ut i).count a : ℤ) = tableLineDegreeTwo.jTil U w t i a) ∧
        ∀ c ∈ Finset.Icc 1 t,
          (GalData.mk lam T (χ 1) ε : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)).chi c = χ c := by
  atlas_forward_decl GlobalTheory.TopWindow.exists_topData_galData
end

section
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TopDict

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

theorem mk_mem_unr_iff {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) (I : Subgroup G) (z : ↥(Z1 π ⊤)) :
    (Submodule.Quotient.mk z : H1 π ⊤) ∈ unr π I ↔ ∃ b, ∀ g ∈ I, (z : G → M) g = π g b - b := by
  constructor
  · rintro ⟨z', ⟨b, hb⟩, h⟩
    obtain ⟨b', -, hb'⟩ := (Submodule.Quotient.eq _).mp h
    refine ⟨b - b', fun g hg => ?_⟩
    have h1 : π g b' - b' = (z' : G → M) g - (z : G → M) g := congrFun hb' g
    rw [hb g hg] at h1
    have h2 : (z : G → M) g = π g b - b - (π g b' - b') := by rw [h1]; abel
    rw [h2, map_sub]
    abel
  · rintro ⟨b, hb⟩
    exact ⟨z, ⟨b, hb⟩, rfl⟩

theorem admissibleExtension_iff_equivariantCoefIso {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ}
    (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (Γ : GalData G Qp LL O) (t : ℕ) (Ut : ZMod n → Multiset ℤ)
    {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (W : Representation O G M) (W' : Representation O G M') (e : M ≃ₗ[O] M') (he : ∀ g x, e (W g x) = W' g (e x))
    (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X)
    (hzz : ∀ g, z' g = LinearEquiv.rTensor X e (z g)) (hz : z ∈ Z1 (twCoef W χ X) ⊤)
    (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0) :
    Admissible PD emb Γ t Ut (Ea W χ hc ⟨z, hz⟩) ↔ Admissible PD emb Γ t Ut (Ea W' χ hc ⟨z', hz'⟩) := by
  obtain ⟨f, hf⟩ := (GlobalTheory.T.equivariantIso_transport_cocycles_extensions W W' e he χ X z z' hzz).2.1 hz hz' hc
  have hf' : ∀ g x, f.symm (Ea W' χ hc ⟨z', hz'⟩ g x) = Ea W χ hc ⟨z, hz⟩ g (f.symm x) :=
    fun g x => f.injective (by rw [hf, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  exact ⟨fun h => h.of_equiv f hf, fun h => h.of_equiv f.symm hf'⟩

theorem WachMod_mem_B1_iff {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) (z : G → M) : z ∈ B1 π ⊤ ↔ ∃ m, ∀ g, z g = π g m - m := by
  constructor
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, Submodule.mem_top, funext fun g => (hm g).symm⟩

set_option maxHeartbeats 8000000 in

theorem topCore_of_typings : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P), GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P →
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P → ∀ (K LL : FinExt l) (hA : CaseA K LL) (lam : ↥(OL LL)),
    Irreducible lam → tableLineDegreeTwo.TopCore (P.PD K) (H.W K 1 LL hA.2.2).emb lam (IK K) := by
  intro l _ P AI hT H hSA hSB hSC K LL hA lam hlam h5 t h w η typ U V _ _ _ _ _ _ _ _ _ _ _ ρ T₀ χ hyp X _ _ _
  let T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := LocLat.mk V ρ hyp.2.2.1 T₀
  have hcard := GlobalTheory.T.card_hodgeTate_jumps_crystalline_eq_dim P AI hT H K LL hA V ρ U hyp.2.2.2.1 hyp.2.2.2.2.1
  obtain ⟨r, D, ε, hHyp, hDt, hcount, hchi⟩ := GlobalTheory.T.exists_numerical_galoisData_localSituation P H K LL hA lam hlam h5 t h w η typ U T χ hyp hcard
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hHyp.1⟩
  let S : TopSit P := ⟨K, LL, _, r, (H.W K 1 LL hA.2.2).emb, D, ⟨lam, T, χ 1, ε⟩, hHyp⟩
  have hkill : ∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0 := by
    obtain ⟨_, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    exact GlobalTheory.T.exists_pow_smul_eq_zero_of_finite_of_not_isUnit (↥(OL LL)) lam hlam.not_isUnit X
  have hCl := GlobalTheory.AdmClosure.admissible_closed S
  obtain ⟨hL0, hLc⟩ := GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hCl (StdAdm.stdAdm S (CrysRules.crysCalc AI hT S) hCl)
  have hpoly : tableLineDegreeTwo.resPoly ρ χ t = tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t := by
    funext g
    change tableLineDegreeTwo.resPoly ρ χ t g = tableLineDegreeTwo.resPoly ρ S.Γ.chi D.t g
    rw [hDt]
    unfold tableLineDegreeTwo.resPoly
    congr 1
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [hchi c hc]
  have key : ∀ (T' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T'.ρ) (z : S.G → ↥L.T ⊗[S.O] X)
      (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤),
      tableLineDegreeTwo.IsAdmCoc (P.PD K) (H.W K 1 LL hA.2.2).emb lam (tableLineDegreeTwo.jTil U w t) (tableLineDegreeTwo.resPoly ρ χ t) L X (χ 1) z ↔
      ∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩) := by
    intro T' L z hz
    rw [hpoly]
    exact exists_congr fun a₀ => forall_congr' fun a => forall_congr' fun _ => forall_congr' fun ha =>
      GlobalTheory.T.admissible_quotientExtension_iff_admissible_ext S (tableLineDegreeTwo.jTil U w t) hcount T' L X z hz a ha

  have ext_iff : ∀ (c : ℕ) {Mc : Type} [AddCommGroup Mc] [Module S.O Mc] (Wc : Representation S.O S.G Mc)
      (e : S.O ≃ₗ[S.O] Mc), (∀ g x, e (S.Γ.Wchi c g x) = Wc g (e x)) →
      ∀ (z₀ : S.G → S.O ⊗[S.O] X) (z : S.G → Mc ⊗[S.O] X), (∀ g, z g = LinearEquiv.rTensor X e (z₀ g)) →
      ∀ (hz₀ : z₀ ∈ Z1 (twCoef (S.Γ.Wchi c) S.Γ.χ₁ X) ⊤) (hz : z ∈ Z1 (twCoef Wc S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea Wc S.Γ.χ₁ ha ⟨z, hz⟩)) ↔
        (∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea (S.Γ.Wchi c) S.Γ.χ₁ ha ⟨z₀, hz₀⟩))) := by
    intro c Mc _ _ Wc e he z₀ z hzz hz₀ hz
    refine exists_congr fun a₀ => forall_congr' fun a => forall_congr' fun _ => forall_congr' fun ha => ?_
    exact (admissibleExtension_iff_equivariantCoefIso (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut (S.Γ.Wchi c) Wc e he S.Γ.χ₁ X z₀ z hzz hz₀ hz ha).symm
  refine ⟨?_, ?_, ?_⟩
  · intro ρ' T₀' hρ' hTT z hz
    have hz' : z ∈ Z1 (twCoef (latRep T₀) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff T₀ X (χ 1)).2 z).1 hz
    rw [key T T₀ z hz', GlobalTheory.T.cocycle_class_admissible S S.Γ.W₀ X hkill (hL0 X).2.1 ⟨z, hz'⟩]
    have hA' := ((hSA K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp.1 hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1
      hHyp.2.2.2.2).2.2.2.2 X).2
    exact (Set.ext_iff.1 hA' (Submodule.Quotient.mk ⟨z, hz'⟩)).trans
      (SetLike.mem_coe.trans (GlobalTheory.T.period_data_dual_exact (P.PD K) T₀ ρ' T₀' X (χ 1) hρ' hTT z hz'))
  · intro c hc Lc z hz
    have hc' := Finset.mem_Icc.1 hc
    have hc1 : c ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨by omega, hc'.2⟩
    have hχc : S.Γ.chi c = χ c := hchi c hc1
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_stableLattice_integralCharacter LL (χ c) Lc
    have he' : ∀ g x, e (S.Γ.Wchi c g x) = latRep Lc g (e x) := fun g x =>
      (congrArg (fun θ : S.G →* S.Oˣ => e (Formalism.GaloisCohomology.scalRep S.O θ g x)) hχc).trans (he g x)
    let z₀ : S.G → S.O ⊗[S.O] X := fun g => (LinearEquiv.rTensor X e).symm (z g)
    have hzz : ∀ g, z g = LinearEquiv.rTensor X e (z₀ g) := fun g => (LinearEquiv.apply_symm_apply _ _).symm
    obtain ⟨hZ, -, hB, -⟩ := GlobalTheory.T.equivariantIso_transport_cocycles_extensions (S.Γ.Wchi c) (latRep Lc) e he' (χ 1) X z₀ z hzz
    have hz' : z ∈ Z1 (twCoef (latRep Lc) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff Lc X (χ 1)).2 z).1 hz
    have hz₀ := hZ.2 hz'
    have hcont := (hyp.2.2.2.2.2 c hc1).2.1
    let Tc : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      LocLat.mk ↥LL.1 (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) (χ c))) (fun x => hcont.mul continuous_const) Lc
    rw [key Tc Lc z hz', ext_iff c (latRep Lc) e he' z₀ z hzz hz₀ hz',
      GlobalTheory.T.cocycle_class_admissible S (S.Γ.Wchi c) X hkill ((hLc c (by omega) (by rw [hDt]; exact hc'.2)) X).2.1 ⟨z₀, hz₀⟩]
    have hB' := hSB K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp c hc'.1 (by rw [hDt]; exact hc'.2) X
    change _ ∈ adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi c) X ↔ _
    rw [show adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi c) X = {0} from hB',
      Set.mem_singleton_iff, Submodule.Quotient.mk_eq_zero]
    change z₀ ∈ B1 (twCoef (S.Γ.Wchi c) S.Γ.χ₁ X) ⊤ ↔ _
    rw [hB, WachMod_mem_B1_iff]
    exact exists_congr fun m => forall_congr' fun g =>
      iff_of_eq (congrArg (fun y => z g = y - m) ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff Lc X (χ 1)).1 g m).symm)
  · intro L₁ z hz
    have h1 : 1 ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨le_rfl, hyp.1⟩
    have hχc : S.Γ.chi 1 = χ 1 := hchi 1 h1
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_stableLattice_integralCharacter LL (χ 1) L₁
    have he' : ∀ g x, e (S.Γ.Wchi 1 g x) = latRep L₁ g (e x) := fun g x =>
      (congrArg (fun θ : S.G →* S.Oˣ => e (Formalism.GaloisCohomology.scalRep S.O θ g x)) hχc).trans (he g x)
    let z₀ : S.G → S.O ⊗[S.O] X := fun g => (LinearEquiv.rTensor X e).symm (z g)
    have hzz : ∀ g, z g = LinearEquiv.rTensor X e (z₀ g) := fun g => (LinearEquiv.apply_symm_apply _ _).symm
    obtain ⟨hZ, -, -, hU⟩ := GlobalTheory.T.equivariantIso_transport_cocycles_extensions (S.Γ.Wchi 1) (latRep L₁) e he' (χ 1) X z₀ z hzz
    have hz' : z ∈ Z1 (twCoef (latRep L₁) (χ 1) X) ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff L₁ X (χ 1)).2 z).1 hz
    have hz₀ := hZ.2 hz'
    have hcont := (hyp.2.2.2.2.2 1 h1).2.1
    let Tc : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      LocLat.mk ↥LL.1 (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) (χ 1))) (fun x => hcont.mul continuous_const) L₁
    rw [key Tc L₁ z hz', ext_iff 1 (latRep L₁) e he' z₀ z hzz hz₀ hz',
      GlobalTheory.T.cocycle_class_admissible S (S.Γ.Wchi 1) X hkill ((hLc 1 le_rfl (by rw [hDt]; exact hyp.1)) X).2.1 ⟨z₀, hz₀⟩]
    have hC' := hSC K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp.1 hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1
      hHyp.2.2.2.2 X
    change _ ∈ adm (P.PD K) (H.W K 1 LL hA.2.2).emb S.Γ D.t D.Ut (S.Γ.Wchi 1) X ↔ _
    rw [hC', GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia_eq_unr]
    rw [SetLike.mem_coe, mk_mem_unr_iff, hU]
    exact exists_congr fun m => forall_congr' fun g => forall_congr' fun _ =>
      iff_of_eq (congrArg (fun y => z g = y - m) ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff L₁ X (χ 1)).1 g m).symm)

end GlobalTheory.TopDict
end

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exactLocalConditions_topCore : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (H : LocHW l P), GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P → ∀ (K LL : FinExt l) (hA : CaseA K LL) (lam : ↥(OL LL)), Irreducible lam → tableLineDegreeTwo.TopCore (P.PD K) (H.W K 1 LL hA.2.2).emb lam (IK K) := by
  atlas_forward_decl GlobalTheory.TopDict.topCore_of_typings
end
