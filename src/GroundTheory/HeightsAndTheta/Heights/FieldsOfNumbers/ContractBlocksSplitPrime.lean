import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PfContractedHypothesesExample
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

section

variable {F : Type*} [Field F] {K : Type*} {ι : K → Type*}

theorem relDim_eq_iff_hasRelDim [Fintype K] (I : Ideal (MRing ι F)) (n : ℕ) :
    relDim I = (n : WithBot (WithTop ℤ)) ↔ IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim I n := by
  unfold relDim IndefiniteRowSideFullHecke.FieldNumbers.HasRelDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x
  have e1 : ((n : ℕ) : WithBot (WithTop ℤ)) = some (some (n : ℤ)) := rfl
  have e2 : ((n + Fintype.card K : ℕ) : WithBot ℕ∞) = some (some (n + Fintype.card K)) := rfl
  rw [e1, e2]
  rcases x with _ | _ | e
  · simp [WithBot.map]
  · simp only [WithBot.map, WithTop.map, Option.map]
    exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  · simp only [WithBot.map, WithTop.map, Option.map]
    constructor
    · intro h
      have h1 : (e : ℤ) - Fintype.card K = n := Option.some.inj (Option.some.inj h)
      have h2 : e = n + Fintype.card K := by omega
      rw [h2]
      exact rfl
    · intro h
      have h1 : e = n + Fintype.card K := Option.some.inj (Option.some.inj h)
      subst h1
      congr 2
      push_cast
      ring

variable [DecidableEq K]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace AddBlockFunctionField

section Projection

variable {F : Type u} [Field F] {K L : Type} {ι : K → Type} {ι₂ : L → Type}

example : MRing (fun k => Sum.elim ι ι₂ ((Function.Embedding.inl : K ↪ K ⊕ L) k)) F =
    MRing ι F := rfl

theorem pullDeg_inl (b : K → ℤ) :
    pullDeg (Function.Embedding.inl : K ↪ K ⊕ L) b = IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := L) b := by
  funext x
  cases x with
  | inl k =>
    exact (Sum.inl_injective.extend_apply b 0 k)
  | inr l =>
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨k, hk⟩
    exact Sum.inl_ne_inr hk

theorem pulledFunField_eq [DecidableEq K] (P' : Ideal (MRing (Sum.elim ι ι₂) F)) [P'.IsPrime] :
    IndefiniteRowSideFullHecke.FieldNumbers.pulledFunField ι₂ P' =
      (homFracDegZero (contractPrime (Function.Embedding.inl : K ↪ K ⊕ L) P')).map
        (contractFracMap Function.Embedding.inl P') := by
  unfold IndefiniteRowSideFullHecke.FieldNumbers.pulledFunField homFracDegZero
  rw [IntermediateField.adjoin_map]
  congr 1
  ext x
  constructor
  · rintro ⟨d, f, g, hf, hg, hgP, rfl⟩
    refine ⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, ?_⟩
    simp [contractFracMap, contractQuot, map_div₀, IndefiniteRowSideFullHecke.FieldNumbers.blockIncl]
    rfl
  · rintro ⟨y, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩
    refine ⟨d, f, g, hf, hg, hgP, ?_⟩
    simp [contractFracMap, contractQuot, map_div₀, IndefiniteRowSideFullHecke.FieldNumbers.blockIncl]
    rfl

theorem relDeg_inl [DecidableEq K] [DecidableEq L] (P' : Ideal (MRing (Sum.elim ι ι₂) F))
    [P'.IsPrime] :
    relDeg (Function.Embedding.inl : K ↪ K ⊕ L) P' = IndefiniteRowSideFullHecke.FieldNumbers.fibreDeg ι₂ P' := by
  unfold relDeg IndefiniteRowSideFullHecke.FieldNumbers.fibreDeg
  rw [pulledFunField_eq]
  rfl

end Projection

section NewBlock

variable {F : Type u} [Field F] {K : Type} {ι : K → Type}

abbrev blockEquiv (K : Type) : Option K ≃ K ⊕ Unit := Equiv.optionEquivSumPUnit K

def addBlockVarEquiv (ι : K → Type) (N : ℕ) :
    (Σ o, addBlock ι N o) ≃ (Σ s, Sum.elim ι (fun _ : Unit => Fin (N + 1)) s) where
  toFun v := match v with
    | ⟨none, i⟩ => ⟨Sum.inr (), i⟩
    | ⟨some k, x⟩ => ⟨Sum.inl k, x⟩
  invFun v := match v with
    | ⟨Sum.inl k, x⟩ => ⟨some k, x⟩
    | ⟨Sum.inr (), i⟩ => ⟨none, i⟩
  left_inv v := by rcases v with ⟨_ | k, x⟩ <;> rfl
  right_inv v := by rcases v with ⟨k | ⟨⟩, x⟩ <;> rfl

theorem pullDeg_some (c : K → ℤ) :
    pullDeg (Function.Embedding.some : K ↪ Option K) c =
      IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := Unit) c ∘ blockEquiv K := by
  funext o
  cases o with
  | some k => exact (Option.some_injective K).extend_apply c 0 k
  | none =>
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨k, hk⟩
    exact Option.some_ne_none k hk

end NewBlock

end AddBlockFunctionField

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem PFDegree.toIndefiniteRowSideFullHecke (hA : ProjectionFormulaDegree.Statement.{u}) :
    IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0} := by
  intro F _ K _ _ L _ _ ι _ ι₂ _ P' hP' n hc hP bs
  have : ∀ s, Fintype (Sum.elim ι ι₂ s) := fun s => match s with
    | .inl k => (inferInstance : Fintype (ι k))
    | .inr l => (inferInstance : Fintype (ι₂ l))
  obtain ⟨-, h⟩ := hA F K (K ⊕ L) Function.Embedding.inl (Sum.elim ι ι₂) P' hP' n
    ((relDim_eq_iff_hasRelDim P' n).mpr hP)
    ((relDim_eq_iff_hasRelDim (IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks ι₂ P') n).mpr hc) bs
  have := hP'.isPrime
  simp only [AddBlockFunctionField.pullDeg_inl, AddBlockFunctionField.relDeg_inl] at h
  exact h

section Split

variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)

def splitBlockEquiv : K ⊕ blockCompl j ≃ K' :=
  Equiv.ofBijective (Sum.elim j Subtype.val) (by
    refine ⟨?_, fun k' => ?_⟩
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (j.injective h)
      · exact absurd ⟨a, h⟩ b.2
      · exact absurd ⟨b, h.symm⟩ a.2
      · exact congrArg Sum.inr (Subtype.ext h)
    · by_cases h : k' ∈ Set.range j
      · obtain ⟨k, rfl⟩ := h
        exact ⟨Sum.inl k, rfl⟩
      · exact ⟨Sum.inr ⟨k', h⟩, rfl⟩)

def splitVarEquiv : (Σ s, splitCoord j ι' s) ≃ (Σ k', ι' k') :=
  Equiv.ofBijective (splitVar j ι') (by
    refine ⟨?_, fun ⟨k', i⟩ => ?_⟩
    · rintro ⟨a | a, x⟩ ⟨b | b, y⟩ h
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
        cases j.injective h1
        cases eq_of_heq h2
        rfl
      · exact absurd ⟨a, congrArg Sigma.fst h⟩ b.2
      · exact absurd ⟨b, (congrArg Sigma.fst h).symm⟩ a.2
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
        cases Subtype.ext h1
        cases eq_of_heq h2
        rfl
    · by_cases h : k' ∈ Set.range j
      · obtain ⟨k, rfl⟩ := h
        exact ⟨⟨Sum.inl k, i⟩, rfl⟩
      · exact ⟨⟨Sum.inr ⟨k', h⟩, i⟩, rfl⟩)

theorem splitVarEquiv_fst (v : Σ s, splitCoord j ι' s) :
    (splitVarEquiv j ι' v).1 = splitBlockEquiv j v.1 := by
  rcases v with ⟨k | l, i⟩ <;> rfl

theorem contractBlocks_splitPrime {F : Type u} [Field F] (P' : Ideal (MRing ι' F)) :
    IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks (fun l : blockCompl j => ι' l.1) (splitPrime j P') =
      contractPrime j P' := by
  ext p
  unfold IndefiniteRowSideFullHecke.FieldNumbers.contractBlocks splitPrime contractPrime IndefiniteRowSideFullHecke.FieldNumbers.blockIncl
  simp only [Ideal.mem_comap]
  have e : rename (splitVar j ι') (rename (fun x : Σ k, ι' (j k) =>
      (⟨Sum.inl x.1, x.2⟩ : Σ s, splitCoord j ι' s)) p) = rename (blockIncl j ι') p := by
    rw [rename_rename]
    rfl
  exact iff_of_eq (congrArg (· ∈ P') e)

theorem pullDeg_split (b : K → ℤ) :
    IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := blockCompl j) b ∘ (splitBlockEquiv j).symm = pullDeg j b := by
  funext k'
  obtain ⟨s, rfl⟩ := (splitBlockEquiv j).surjective k'
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rcases s with k | l
  · exact (j.injective.extend_apply b 0 k).symm
  · show (0 : ℤ) = Function.extend j b 0 l.1
    rw [Function.extend_apply' _ _ _ (fun h => l.2 h)]
    rfl

theorem relDim_splitPrime {F : Type u} [Field F] [Fintype K] [Fintype K'] [Fintype (blockCompl j)]
    (P' : Ideal (MRing ι' F)) : relDim (splitPrime j P') = relDim P' := by
  have e : MRing (splitCoord j ι') F ⧸ splitPrime j P' ≃+* MRing ι' F ⧸ P' :=
    Ideal.quotientEquiv _ _ (renameEquiv F (splitVarEquiv j ι')).toRingEquiv
      (Ideal.map_comap_of_surjective _ (renameEquiv F (splitVarEquiv j ι')).surjective P').symm
  unfold relDim
  rw [ringKrullDim_eq_of_ringEquiv e, Fintype.card_congr (splitBlockEquiv j)]

end Split

theorem contract_funField_le (h₁ : RenameMultiHomog.Statement.{u}) {F : Type u} [Field F]
    {K K' : Type} [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type}
    (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' := by
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩
  refine IntermediateField.subset_adjoin _ _ ⟨Function.extend j d 0, rename (blockIncl j ι') f,
    rename (blockIncl j ι') g, h₁ F K K' j _ ι' _ (fun _ => rfl) f d hf,
    h₁ F K K' j _ ι' _ (fun _ => rfl) g d hg, hgP, ?_⟩
  simp [contractFracMap, contractQuot, map_div₀]
  rfl

theorem PFDegree.split_model_to_place_model (h₁ : RenameMultiHomog.Statement.{u})
    (h₂ : RenameIntNum.Statement.{u}) (h₃ : RenameMultiProjPrime.Statement.{u})
    (h₄ : SplitRelDeg.Statement.{u}) (hB : IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0}) :
    ProjectionFormulaDegree.Statement.{u} := by
  classical
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP hc bs
  have := hP'.isPrime
  refine ⟨contract_funField_le h₁ j P', ?_⟩
  have hQ : IsMultiProjPrime (splitPrime j P') :=
    h₃ F _ K' _ ι' (splitBlockEquiv j) (splitVarEquiv j ι') (splitVarEquiv_fst j ι') P' hP'
  have h := hB F K (blockCompl j) (fun k => ι' (j k)) (fun l => ι' l.1) (splitPrime j P') hQ n
    (by
      rw [contractBlocks_splitPrime]
      exact (relDim_eq_iff_hasRelDim _ n).mp hc)
    (by
      refine (relDim_eq_iff_hasRelDim _ n).mp ?_
      rw [relDim_splitPrime]
      exact hP) bs
  rw [← AddBlockFunctionField.relDeg_inl, ← h₄, contractBlocks_splitPrime] at h
  rw [← h]
  have h2 := h₂ F _ K' _ ι' (splitBlockEquiv j) (splitVarEquiv j ι') (splitVarEquiv_fst j ι') P' n
    (fun i => IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := blockCompl j) (bs i))
  simp only [pullDeg_split] at h2
  exact h2.symm

theorem PFDegree.equiv (h₁ : RenameMultiHomog.Statement.{u})
    (h₂ : RenameIntNum.Statement.{u}) (h₃ : RenameMultiProjPrime.Statement.{u})
    (h₄ : SplitRelDeg.Statement.{u}) :
    ProjectionFormulaDegree.Statement.{u} ↔ IndefiniteRowSideFullHecke.FieldNumbers.PFDegree.Statement.{u, 0, 0, 0} :=
  ⟨PFDegree.toIndefiniteRowSideFullHecke, PFDegree.split_model_to_place_model h₁ h₂ h₃ h₄⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
