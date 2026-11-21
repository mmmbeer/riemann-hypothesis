import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParameterTransferTypes
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra

section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField

namespace GlobalTheory.LiftOntoCompare

section Hilbert

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (θ : V →ₗ[ℂ] W) {X : Submodule ℂ V} {M : Submodule ℂ W}

theorem disjoint_map_adjoint_ker (M : Submodule ℂ W) : Disjoint (M.map (LinearMap.adjoint θ)) (LinearMap.ker θ) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨m, -, rfl⟩ h
  have h0 : θ (LinearMap.adjoint θ m) = 0 := h
  have : inner ℂ (LinearMap.adjoint θ m) (LinearMap.adjoint θ m) = 0 := by
    rw [LinearMap.adjoint_inner_left, h0, inner_zero_right]
  exact inner_self_eq_zero.1 this

end Hilbert

section Readings

open GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
  (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ)

end Readings

example : ∃ θ : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] ℂ, (⊤ : Submodule ℂ _).map θ = ⊤ ∧
    (⊤ : Submodule ℂ ℂ).map (LinearMap.adjoint θ) ≠ ⊤ := by
  refine ⟨(EuclideanSpace.projₗ (0 : Fin 2)), ?_, fun h => ?_⟩
  · rw [eq_top_iff]
    intro z _
    exact ⟨EuclideanSpace.single 0 z, trivial, by simp⟩
  · have := disjoint_map_adjoint_ker (EuclideanSpace.projₗ (0 : Fin 2) : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] ℂ) ⊤
    rw [h, Submodule.disjoint_def] at this
    have h1 := this (EuclideanSpace.single 1 1) trivial (by simp)
    have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 1) h1
    simp at h2

end GlobalTheory.LiftOntoCompare

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes GlobalTheory.Hk3 GlobalTheory.SplitHeckeAdj

namespace GlobalTheory.LiftOntoCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Abstract

variable {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* H}
  {ρ : Γ →* Module.End ℂ W} {J : Subgroup H} {χ : J →* ℂˣ} {Φ : H → W}

theorem mem_adForms_iff : Φ ∈ Bridge.AdForms ι ρ J χ ↔
    (∀ γ u, Φ (ι γ * u) = ρ γ (Φ u)) ∧ ∀ u k (hk : k ∈ J), Φ (u * k) = (χ ⟨k, hk⟩ : ℂ) • Φ u :=
  ⟨fun h => ⟨fun γ u => by simpa using h γ u 1, fun u k hk => by simpa using h 1 u ⟨k, hk⟩⟩,
    fun h γ u k => by rw [h.2 _ _ k.2, h.1]⟩

theorem eq_of_dual {x y : W} (h : ∀ ℓ : W →ₗ[ℂ] ℂ, ℓ x = ℓ y) : x = y :=
  sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => by rw [map_sub, h ℓ, sub_self])

end Abstract

section General

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (c : CoefA V)

variable {c}

theorem hasType_form {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ρ : GQ V →* Module.End ℂ W} {Φ : Bridge.Gf V → W}
    (hΦ : Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ)
    (ℓ : W →ₗ[ℂ] ℂ) : HasType V β (flag1L L) fun g => ℓ (Φ (fin V g)) := fun κ hκ g =>
  (congrArg (fun u => ℓ (Φ u)) ((fin V).map_mul g κ)).trans
    ((congrArg ℓ ((mem_adForms_iff.1 hΦ).2 (fin V g) _ ((mem_J V β L hκ.1).2 hκ))).trans (ℓ.map_smul _ _))

theorem forall_fin {p : Bridge.Gf V → Prop} (h : ∀ g ∈ GfC V, p (fin V g)) (u : Bridge.Gf V) : p u :=
  (fin_lift V u).elim fun g hg => hg.2 ▸ h g hg.1

theorem hkF_mem {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ρ : GQ V →* Module.End ℂ W} {w : Pl D.host.E}
    (a : List ℤ →₀ ℂ) (h3 : ∀ Φ, HasType V β (flag1L L) Φ → HasType V β (flag1L L) (hk V w a Φ))
    {Φ : Bridge.Gf V → W} (hΦ : Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ) :
    hkF V w a Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ := by
  have hc : ∀ (ℓ : W →ₗ[ℂ] ℂ) g, hk V w a (fun g => ℓ (Φ (fin V g))) g = ℓ (hkF V w a Φ (fin V g)) := fun ℓ g => by
    rw [GlobalTheory.LevOp.hk_apply]
    simp only [hkF, Finsupp.sum, map_sum, LinearMap.map_smul, smul_eq_mul, heckeLin_apply, MonoidHom.map_mul]
  refine mem_adForms_iff.2 ⟨fun γ u => ?_, fun u k => ?_⟩
  · simp only [hkF, Finsupp.sum, mul_assoc, (mem_adForms_iff.1 hΦ).1, map_sum, LinearMap.map_smul]
  · refine forall_fin (p := fun k => ∀ hk : k ∈ (levEnv V β L).J,
      hkF V w a Φ (u * k) = ((levEnv V β L).χ ⟨k, hk⟩ : ℂ) • hkF V w a Φ u) (fun κ hκ hk => ?_) k
    refine forall_fin (p := fun u => hkF V w a Φ (u * fin V κ) = ((levEnv V β L).χ ⟨fin V κ, hk⟩ : ℂ) • hkF V w a Φ u)
      (fun g _ => eq_of_dual fun ℓ => ?_) u
    have := h3 _ (hasType_form hΦ ℓ) κ ((mem_J V β L hκ).1 hk) g
    rw [hc, hc, MonoidHom.map_mul] at this
    exact this.trans (ℓ.map_smul _ _).symm

theorem one_notMem (w : Pl D.host.E) (n : ℕ) : ((1 ^ n : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  rw [one_pow, Nat.cast_one]
  exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top

end General

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem offS_iff_good (t : T) (w : Pl D.host.E) : OffS D (badS R t) w ↔ Good R t w := by
  classical
  rw [GlobalTheory.GoodPrimes.offS_iff]
  unfold badS
  simp only [Finset.mem_image, Finset.mem_union, not_exists, not_and]
  refine forall₂_congr fun PP _ => ⟨fun h => ⟨fun e => h (by rw [e]), fun e => h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩, fun h e => ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h1 | h1
  · exact h.1 h1.symm
  · exact h.2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1)

theorem exists_opsV (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (i : Fin D.R.m) (t : T) : ∃ h, IsOpsV R i t h := by
  have key : ∀ w a, ∃ s : Module.End ℂ (R.HV i t).H, Good R t w → ∀ x, (R.HV i t).e (s x) = hkF (Vc D i) w a ((R.HV i t).e x) := by
    intro w a
    by_cases hw : Good R t w
    swap
    · exact ⟨0, fun h => absurd h hw⟩
    refine (hL.βV i).elim fun n hn => ?_
    have h3 := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) _ (flag1L (R.datVt i t)) hn w (one_notMem w n) hw).2.2.1 a
    exact (GlobalTheory.DefiniteOps.exists_lift (R.HV i t) _ _ (hM.HV i t)
      (opOf (GlobalTheory.DefiniteOps.rtr (fin (Vc D i)) (R.cV i).W) w a)
      fun Φ hΦ => GlobalTheory.DefiniteOps.hkF_eq (Vc D i) w a Φ ▸ hkF_mem a h3 hΦ).imp
      fun s hs _ x => (hs x).trans (GlobalTheory.DefiniteOps.hkF_eq _ _ _ _).symm
  choose h hh using key
  exact ⟨h, fun w hw c x => hh w c hw x⟩

section Levels

variable (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ)

end Levels

section Compare

variable (R) (F : Face D A)

variable {R}

variable (R)

end Compare

end GlobalTheory.LiftOntoCompare

end
end
