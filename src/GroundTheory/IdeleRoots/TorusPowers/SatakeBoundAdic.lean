import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInSatake
import GroundTheory.AutomorphicForms.MacdonaldHecke
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open Finset

variable {q : ℝ}

def wt (N : ℕ) (S : Finset (Fin N)) : ℕ := ∑ i ∈ S, (N - 1 - (i : ℕ))

def pw (q : ℝ) (N : ℕ) (S : Finset (Fin N)) : ℝ := q ^ wt N S / q ^ S.card.choose 2

end SatakeBound

end GroundTheory.BlockD
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_perm_mem_iff {N : ℕ} {A B : Finset (Fin N)} (h : A.card = B.card) :
    ∃ σ : Equiv.Perm (Fin N), ∀ x, σ x ∈ B ↔ x ∈ A := by
  classical
  have e1 : {x // x ∈ A} ≃ {x // x ∈ B} := Fintype.equivOfCardEq (by simp [h])
  have e2 : {x // x ∉ A} ≃ {x // x ∉ B} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]; simp [h])
  refine ⟨(Equiv.sumCompl (· ∈ A)).symm.trans ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl (· ∈ B))),
    fun x => ?_⟩
  by_cases hx : x ∈ A
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hx, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact ⟨fun _ => hx, fun _ => (e1 ⟨x, hx⟩).2⟩
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hx, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact ⟨fun h' => absurd h' (e2 ⟨x, hx⟩).2, fun h' => absurd h' hx⟩

theorem lamS_comp_of_mem_iff {N : ℕ} {A B : Finset (Fin N)} {σ : Equiv.Perm (Fin N)}
    (hσ : ∀ x, σ x ∈ B ↔ x ∈ A) : lamS B ∘ σ = lamS A := by
  funext x
  simp only [Function.comp_apply, lamS, hσ]

def lowSet (N k : ℕ) : Finset (Fin N) := univ.filter fun i => (i : ℕ) < k

section Values

variable {n : ℕ} {ω : GL (Fin n) F → ℂ}
  (hR : ∀ g, ∀ k ∈ integralGL F n, ω (g * k) = ω g)
  (hL : ∀ g, ∀ k ∈ integralGL F n, ω (k * g) = ω g)
include hR hL

end Values

section ValuesCons

variable {N : ℕ} {ω : GL (Fin (N + 1)) F → ℂ}
  (hR : ∀ g, ∀ k ∈ integralGL F (N + 1), ω (g * k) = ω g)
  (hL : ∀ g, ∀ k ∈ integralGL F (N + 1), ω (k * g) = ω g)
include hR hL

end ValuesCons

variable {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

def heckeEig (ω : GL (Fin n) F → ℂ) (r : ℕ) : ℂ :=
  ∑ S ∈ powersetCard r (univ : Finset (Fin n)), ∑ c : Pairs S → 𝓀[F], ω (gMat S c)

end SatakeBound

end GroundTheory.BlockD
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open HeckeCharacterZeroLocus.ThmBIn

section Group

variable {G : Type} [Group G] {K : Subgroup G} {α : G} {R : Finset G}


end Group

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem one_apply_mem_integer (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
  rw [Matrix.one_apply]
  split_ifs
  · exact (𝒪[F]).one_mem
  · exact (𝒪[F]).zero_mem

theorem unipC_mem_integralGL (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) : unipC S c ∈ integralGL F n := by
  rw [mem_integralGL_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change (1 + cMat S c) i j ∈ 𝒪[F]
    rw [Matrix.add_apply]
    exact (𝒪[F]).add_mem (one_apply_mem_integer i j) (cMat_mem c i j)
  · change (1 - cMat S c) i j ∈ 𝒪[F]
    rw [Matrix.sub_apply]
    exact (𝒪[F]).sub_mem (one_apply_mem_integer i j) (cMat_mem c i j)

theorem exists_torusPow_lamS_eq {A B : Finset (Fin n)} (h : A.card = B.card) :
    ∃ P ∈ integralGL F n, torusPow F n (lamS A) = P⁻¹ * torusPow F n (lamS B) * P := by
  obtain ⟨σ, hσ⟩ := exists_perm_mem_iff h
  refine ⟨permGL F σ, GLnLocal.permGL_mem_integralGL F n σ, ?_⟩
  rw [permGL_conj_torusPow, lamS_comp_of_mem_iff hσ]

def reps (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n r : ℕ) : Finset (GL (Fin n) F) :=
  open Classical in (powersetCard r (univ : Finset (Fin n))).biUnion fun S => univ.image (gMat S)

theorem mk_gMat_eq {S S' : Finset (Fin n)} {c : Pairs S → 𝓀[F]} {c' : Pairs S' → 𝓀[F]}
    (h : (QuotientGroup.mk (gMat S c) : GL (Fin n) F ⧸ integralGL F n) = QuotientGroup.mk (gMat S' c')) :
    S = S' := by
  have hk : (gMat S c)⁻¹ * gMat S' c' ∈ integralGL F n := QuotientGroup.eq.1 h
  have e : gMat S' c' = unipC S c * torusPow F n (lamS S) * ((gMat S c)⁻¹ * gMat S' c') := by
    simp only [gMat]
    group
  have := iwasawaExponent_eq F n (unipC_mem_unipotent S c) hk (l := lamS S)
  rw [← e, iwasawaExponent_gMat] at this
  exact lamS_injective this.symm

theorem gMat_injective' (S : Finset (Fin n)) : Function.Injective (gMat (F := F) S) :=
  fun _ _ h => gMat_injective S (congrArg QuotientGroup.mk h)

theorem mem_reps {r : ℕ} {γ : GL (Fin n) F} :
    γ ∈ reps F n r ↔ ∃ S ∈ powersetCard r (univ : Finset (Fin n)), ∃ c, gMat S c = γ := by
  classical
  simp only [reps, mem_biUnion, mem_image, mem_univ, true_and]

theorem sum_reps {M : Type*} [AddCommMonoid M] (r : ℕ) (f : GL (Fin n) F → M) :
    ∑ γ ∈ reps F n r, f γ = ∑ S ∈ powersetCard r (univ : Finset (Fin n)), ∑ c : Pairs S → 𝓀[F], f (gMat S c) := by
  classical
  rw [reps, sum_biUnion]
  · refine sum_congr rfl fun S _ => ?_
    rw [sum_image fun c _ c' _ h => gMat_injective' S h]
  · intro S _ S' _ hne
    rw [Function.onFun, disjoint_left]
    intro x hx hx'
    obtain ⟨c, -, rfl⟩ := mem_image.1 hx
    obtain ⟨c', -, hc'⟩ := mem_image.1 hx'
    exact hne (mk_gMat_eq (congrArg QuotientGroup.mk hc'.symm))


end SatakeBound

end GroundTheory.BlockD
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open HeckeCharacterZeroLocus.ThmBIn IsDedekindDomain NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa
  Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem valued_uniformizer_eq :
    Valued.v (uniformizer (w.adicCompletion K) : w.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  have hS : (Valuation.integer (ValuativeRel.valuation (w.adicCompletion K))) =
      (w.adicCompletionIntegers K).toSubring := by
    ext x
    exact GroundTheory.Global.mem_valuationInteger_iff w x
  let e := RingEquiv.subringCongr hS
  have hirr : Irreducible (e (uniformizer (w.adicCompletion K))) :=
    (MulEquiv.irreducible_iff e).2 (irreducible_uniformizer _)
  have := GroundTheory.Global.valued_of_irreducible (v := w) (K := K)
    (ϖ := ⟨(e (uniformizer (w.adicCompletion K)) : w.adicCompletion K), (e _).2⟩) (by exact hirr)
  simpa [e] using this

theorem valued_le_one_of_mem {x : w.adicCompletion K} (hx : x ∈ 𝒪[w.adicCompletion K]) :
    Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K w).1
    ((GroundTheory.Global.mem_valuationInteger_iff w x).1 hx)


variable {w}

end SatakeBound

end GroundTheory.BlockD
end
end
