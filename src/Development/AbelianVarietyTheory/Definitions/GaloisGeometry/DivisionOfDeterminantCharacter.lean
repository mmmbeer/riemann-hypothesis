import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.X0OfStarCondition
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
import Development.AbelianVarietyTheory.Definitions.Divisors.GenTyL
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.RoadW

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def SatAtU (U : Submodule ℂ (UA E a → ℂ)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ ∧
    GlobalTheory.LGrp.HasSatakeGL σ.ρ B

def HasRepU (ι : Qbar l ≃+* ℂ) (U : Submodule ℂ (UA E a → ℂ)) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous r ∧ IsSSRep r ∧ ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → w ∉ S → ∀ B : Multiset ℂˣ, SatAtU U w B →
    (((l : ℕ) : 𝓞 E) ∉ w.asIdeal → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
    (((l : ℕ) : 𝓞 E) ∈ w.asIdeal → SstAt r w ∧ GlobalTheory.CongL.CrysDRU U ι r w ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
        (hj : Pst.Induces Bw), (IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)) ∧
        ∀ g : Weil h, (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)).charPol g = (GlobalTheory.RoadU.satWD h a B).charPol g)

def RowStarCoreU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 E))), NonSplitSet T → (∀ w ∈ S, IsSplitAt w) →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U S r

def RowStarCoreAtU : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 E))), NonSplitSet T → (∀ w ∈ S, IsSplitAt w) →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → (∀ w, ¬ Apart w w₀ → w ∈ S) →
    ∀ U : Submodule ℂ (UA E a → ℂ), IsAutRepU U → (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U S r

theorem HasRepU.mono {ι : Qbar l ≃+* ℂ} {U : Submodule ℂ (UA E a → ℂ)} {S S' : Finset (HeightOneSpectrum (𝓞 E))} (hS : S ⊆ S')
    {r : G E Ω →* GL (Fin a) (Qbar l)} (h : HasRepU ι U S r) : HasRepU ι U S' r :=
  ⟨h.1, h.2.1, fun w hw hn => h.2.2 w hw fun hm => hn (hS hm)⟩

theorem finite_not_apart (w₀ : HeightOneSpectrum (𝓞 E)) : {w : HeightOneSpectrum (𝓞 E) | ¬ Apart w w₀}.Finite := by
  set p := w₀.under (𝓞 (maximalRealSubfield E))
  haveI := p.isMaximal
  have hf : (p.asIdeal.primesOver (𝓞 E)).Finite := IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 E)
  refine (hf.preimage (f := fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal)
    (fun x _ y _ e => HeightOneSpectrum.ext e)).subset fun w hw => ?_
  have e : w.under (𝓞 (maximalRealSubfield E)) = p := not_not.1 hw
  exact ⟨w.isPrime, ⟨by rw [← e]; rfl⟩⟩

def nearPlaces (w₀ : HeightOneSpectrum (𝓞 E)) : Finset (HeightOneSpectrum (𝓞 E)) :=
  (finite_not_apart w₀).toFinset

theorem mem_nearPlaces {w w₀ : HeightOneSpectrum (𝓞 E)} : w ∈ nearPlaces w₀ ↔ ¬ Apart w w₀ :=
  Set.Finite.mem_toFinset _

theorem isSplitAt_of_not_apart {w w₀ : HeightOneSpectrum (𝓞 E)} (h₀ : IsSplitAt w₀) (h : ¬ Apart w w₀) : IsSplitAt w := by
  have e := not_not.1 h
  by_cases hw : w = w₀
  · exact hw ▸ h₀
  · exact ⟨w₀, Ne.symm hw, e.symm⟩

theorem RowStarCoreAtU.near (h : RowStarCoreAtU) (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (hT : NonSplitSet T) {w₀ : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal) (h₀ : IsSplitAt w₀)
    {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) (hu : ∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) :
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U (nearPlaces w₀) r :=
  h E Ω l ι a ha _ T hT (fun _ hw => isSplitAt_of_not_apart h₀ (mem_nearPlaces.1 hw)) w₀ hl h₀
    (fun _ hw => mem_nearPlaces.2 hw) U hU hu

example (w₀ : HeightOneSpectrum (𝓞 E)) : w₀ ∈ nearPlaces w₀ := mem_nearPlaces.2 (not_apart_self w₀)

example (h : RowStarCoreU) (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) : ∃ r : G E Ω →* GL (Fin a) (Qbar l),
    HasRepU ι (Submodule.span ℂ {(fun _ => 1 : UA E a → ℂ)}) ∅ r :=
  h E Ω l ι a ha ∅ ∅ nonSplitSet_empty (fun _ hw => absurd hw (Finset.notMem_empty _)) _ isAutRepU_const
    fun w _ _ => isUnramU_const w

example (h : RowStarCoreAtU) (ι : Qbar l ≃+* ℂ) (ha : 1 ≤ a) {w₀ : HeightOneSpectrum (𝓞 E)} (hl : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal)
    (h₀ : IsSplitAt w₀) : ∃ r : G E Ω →* GL (Fin a) (Qbar l),
      HasRepU ι (Submodule.span ℂ {(fun _ => 1 : UA E a → ℂ)}) (nearPlaces w₀) r :=
  h.near ι ha nonSplitSet_empty hl h₀ isAutRepU_const fun w _ _ => isUnramU_const w

end GlobalTheory.RoadW

end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.RoadW GlobalTheory.CongL Polynomial

namespace GlobalTheory.RoadWGeo

def Lacunary (J : Finset ℤ) : Prop :=
  ∀ A B : Finset ℤ, A ⊆ J → B ⊆ J → Disjoint A B → A.Nonempty → B.Nonempty →
    (B.card : ℤ) * A.sum id ≠ (A.card : ℤ) * B.sum id

theorem Lacunary.mono {J K : Finset ℤ} (h : Lacunary J) (hK : K ⊆ J) : Lacunary K :=
  fun A B hA hB => h A B (hA.trans hK) (hB.trans hK)

theorem lacunary_of_growth {J : Finset ℤ} (hpos : ∀ x ∈ J, 0 < x) (hg : ∀ x ∈ J, ∀ y ∈ J, x < y → (J.card : ℤ) * x < y) :
    Lacunary J := by
  classical
  have key : ∀ A B : Finset ℤ, A ⊆ J → B ⊆ J → B.Nonempty → ∀ m ∈ A, (∀ b ∈ B, b < m) →
      (A.card : ℤ) * B.sum id < (B.card : ℤ) * A.sum id := by
    intro A B hA hB hBn m hm hlt
    have h1 : m ≤ A.sum id := Finset.single_le_sum (f := id) (fun x hx => (hpos x (hA hx)).le) hm
    have hc : (A.card : ℤ) ≤ J.card := by exact_mod_cast Finset.card_le_card hA
    have h2 : ∑ b ∈ B, (A.card : ℤ) * b < ∑ _b ∈ B, m := by
      refine Finset.sum_lt_sum_of_nonempty hBn fun b hb => ?_
      have := hg b (hB hb) m (hA hm) (hlt b hb)
      have := mul_le_mul_of_nonneg_right hc (hpos b (hB hb)).le
      linarith
    rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : (B.card : ℤ) * m ≤ B.card * A.sum id := mul_le_mul_of_nonneg_left h1 (by positivity)
    exact lt_of_lt_of_le h2 h3
  intro A B hA hB hd hAn hBn
  have hne : (A ∪ B).Nonempty := hAn.mono Finset.subset_union_left
  have hmax : ∀ x ∈ A ∪ B, x ≤ (A ∪ B).max' hne := fun x hx => Finset.le_max' _ _ hx
  rcases Finset.mem_union.1 (Finset.max'_mem _ hne) with hm | hm
  · refine (key A B hA hB hBn _ hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_right _ hb)) ?_).ne'
    intro e
    exact Finset.disjoint_left.1 hd hm (e ▸ hb)
  · refine (key B A hB hA hAn _ hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_left _ hb)) ?_).ne
    intro e
    exact Finset.disjoint_left.1 hd hb (e ▸ hm)

theorem not_lacunary_three (k : ℤ) : ¬ Lacunary ({k, k + 1, k + 2} : Finset ℤ) := by
  intro h
  have h02 : k ≠ k + 2 := by omega
  refine h {k, k + 2} {k + 1} ?_ ?_ ?_ (by simp) (by simp) ?_
  · intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · simp only [Finset.disjoint_singleton_right, Finset.mem_insert, Finset.mem_singleton]; omega
  · rw [Finset.sum_pair h02, Finset.card_pair h02]; simp; ring

def wtJumps {a : ℕ} (lam : DomWeight a) : Finset ℤ :=
  Finset.univ.image fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k

theorem strictMono_jump {a : ℕ} (lam : DomWeight a) : StrictMono fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k := by
  intro i j hij
  have h1 := lam.anti hij.le
  have h2 : (i : ℕ) < j := hij
  simp only
  omega

theorem card_wtJumps {a : ℕ} (lam : DomWeight a) : (wtJumps lam).card = a := by
  rw [wtJumps, Finset.card_image_of_injective _ (strictMono_jump lam).injective]; simp

theorem wtJumps_val {a : ℕ} (lam : DomWeight a) :
    (wtJumps lam).val.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [wtJumps, Finset.image_val_of_injOn (strictMono_jump lam).injective.injOn, infOfWeight, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp]
  push_cast
  ring

example : ¬ Lacunary (wtJumps (⟨fun _ => 0, antitone_const⟩ : DomWeight 3)) := by
  have : wtJumps (⟨fun _ => 0, antitone_const⟩ : DomWeight 3) = {0, 0 + 1, 0 + 2} := by
    simp only [wtJumps]; decide
  rw [this]
  exact not_lacunary_three 0

example : Lacunary {1, 10, 100} := lacunary_of_growth (by decide) (by decide)

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime]

def SeedCase (a : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 E))) (w₀ : HeightOneSpectrum (𝓞 E))
    (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  NonSplitSet T ∧ (∀ w ∈ S, IsSplitAt w) ∧ ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal ∧ IsSplitAt w₀ ∧ w₀ ∈ S ∧
    IsAutRepU U ∧ (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) ∧ ScU U w₀

def ESAt {d : ℕ} (ι : Qbar l ≃+* ℂ) (ρ : G E Ω →* GL (Fin d) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂ) :
    Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := E) A, ρ s = 1) ∧
    ∀ σ : G E Ω, IsFrob A (normV w) σ →
      aeval (ρ σ⁻¹ : Matrix (Fin d) (Fin d) (Qbar l)) (((B.map fun b => X - C b).prod).map ι.symm.toRingHom) = 0

def LacWtAt {a : ℕ} (ι : Qbar l ≃+* ℂ) (v' : HeightOneSpectrum (𝓞 E)) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∃ τ : E →+* ℂ, OverPl ι τ v' ∧ ∃ lam : DomWeight a, HasWeightAt U τ lam ∧ Lacunary (wtJumps lam)

end GlobalTheory.RoadWGeo

namespace GlobalTheory.Published

open GlobalTheory.RoadWGeo

end GlobalTheory.Published

end
end
