import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places

section
open NumberField

namespace GroundTheory.Heights₂.Theta

noncomputable section

section Places

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsUnramifiedAtFinitePlaces : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P.ramificationIdx (𝓞 F) = 1

end Places

section Example

open Complex

def sqrtNeg3 : ℂ := I * (Real.sqrt 3 : ℝ)

def sqrtNeg7 : ℂ := I * (Real.sqrt 7 : ℝ)

def sqrtNegEleven : ℂ := I * (Real.sqrt 11 : ℝ)

def exE : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {sqrtNeg3, sqrtNeg7, sqrtNegEleven}

def exF : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {((Real.sqrt 21 : ℝ) : ℂ), ((Real.sqrt 33 : ℝ) : ℂ)}

lemma isIntegral_of_sq {x : ℂ} {a : ℚ} (h : x ^ 2 = (a : ℂ)) : IsIntegral ℚ x := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [h]
  exact isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := a)

lemma sqrtNeg_sq (n : ℕ) : (I * (Real.sqrt n : ℝ) : ℂ) ^ 2 = ((-n : ℚ) : ℂ) := by
  rw [mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  push_cast; ring

lemma sqrt_sq_nat (n : ℕ) : ((Real.sqrt n : ℝ) : ℂ) ^ 2 = ((n : ℚ) : ℂ) := by
  rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  push_cast; ring

instance : FiniteDimensional ℚ exE := by
  unfold exE
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · have h := sqrtNeg_sq 3
    simp only [Nat.cast_ofNat] at h
    exact isIntegral_of_sq h
  · have h := sqrtNeg_sq 7
    simp only [Nat.cast_ofNat] at h
    exact isIntegral_of_sq h
  · have h := sqrtNeg_sq 11
    simp only [Nat.cast_ofNat] at h
    exact isIntegral_of_sq h

instance : FiniteDimensional ℚ exF := by
  unfold exF
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · have h := sqrt_sq_nat 21
    simp only [Nat.cast_ofNat] at h
    exact isIntegral_of_sq h
  · have h := sqrt_sq_nat 33
    simp only [Nat.cast_ofNat] at h
    exact isIntegral_of_sq h

instance : NumberField exE where

instance : NumberField exF where

lemma sqrt_mul_nat (m n : ℕ) :
    ((Real.sqrt ((m * n : ℕ) : ℝ) : ℝ) : ℂ) =
      -((I * (Real.sqrt m : ℝ)) * (I * (Real.sqrt n : ℝ))) := by
  have h : (I * (Real.sqrt m : ℝ)) * (I * (Real.sqrt n : ℝ)) =
      I ^ 2 * ((Real.sqrt m * Real.sqrt n : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, I_sq, ← Real.sqrt_mul (Nat.cast_nonneg m)]
  push_cast; ring

lemma exF_le_exE : exF ≤ exE := by
  unfold exF
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have h3 : sqrtNeg3 ∈ exE := IntermediateField.subset_adjoin _ _ (by simp)
  have h7 : sqrtNeg7 ∈ exE := IntermediateField.subset_adjoin _ _ (by simp)
  have h11 : sqrtNegEleven ∈ exE := IntermediateField.subset_adjoin _ _ (by simp)
  rcases hx with rfl | rfl
  · have e := sqrt_mul_nat 3 7
    norm_num at e
    rw [SetLike.mem_coe, e]
    exact neg_mem (mul_mem h3 h7)
  · have e := sqrt_mul_nat 3 11
    norm_num at e
    rw [SetLike.mem_coe, e]
    exact neg_mem (mul_mem h3 h11)

instance : Algebra exF exE := (IntermediateField.inclusion exF_le_exE).toRingHom.toAlgebra

end Example

end

end GroundTheory.Heights₂.Theta
end

section
noncomputable section

namespace GroundTheory.Heights₂.Theta

open NumberField NumberField.InfinitePlace IsDedekindDomain ComplexConjugate
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open scoped NumberField.AdeleRing nonZeroDivisors

section Objects

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsCMQuadratic : Prop :=
  IsTotallyReal F ∧ IsTotallyComplex E ∧ Module.finrank F E = 2

def RootsOfUnityArePlusMinusOne : Prop :=
  ∀ ζ : Eˣ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → ζ = 1 ∨ ζ = -1

variable {F E}

def IsCMType (Ψ : Finset (E →+* ℂ)) : Prop :=
  ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ

open Classical in

def extAt (τ : E →+* ℂ) : (InfinitePlace.mk τ).Completion →+* ℂ :=
  if (InfinitePlace.mk τ).embedding = τ then Completion.extensionEmbedding (InfinitePlace.mk τ)
  else (starRingEnd ℂ).comp (Completion.extensionEmbedding (InfinitePlace.mk τ))

def HasAngularType (χ : HeckeCharacter E) (τ : E →+* ℂ) (k : ℤ) : Prop :=
  ∀ z : ((InfinitePlace.mk τ).Completion)ˣ,
    ((χ.infiniteComponent (InfinitePlace.mk τ) z : Circle) : ℂ) =
      (extAt τ (z : (InfinitePlace.mk τ).Completion) /
        (‖extAt τ (z : (InfinitePlace.mk τ).Completion)‖ : ℂ)) ^ k

def HasQuotientType (χ : HeckeCharacter E) (τ : E →+* ℂ) (e : ℤ) : Prop :=
  ∀ z : ((InfinitePlace.mk τ).Completion)ˣ,
    ((χ.infiniteComponent (InfinitePlace.mk τ) z : Circle) : ℂ) =
      (extAt τ (z : (InfinitePlace.mk τ).Completion) /
        conj (extAt τ (z : (InfinitePlace.mk τ).Completion))) ^ (-e)

def IsUnramifiedAt (χ : HeckeCharacter E) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ a ∈ unitsLevel (K := E) w 0, χ.localComponent w a = 1

variable (F) in

def IsTrivialOnBase (χ : HeckeCharacter E) : Prop :=
  ∀ x : IdeleClassGroup F, χ (ideleClassMap F E x) = 1

variable (E) in

def IsQuadraticCharacterOf (η : HeckeCharacter F) : Prop :=
  ∀ x : IdeleClassGroup F, η x = 1 ↔ x ∈ (ideleClassNorm F E).range

def conjPlace (c : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  comapPrime (c : E ≃+* E) w

def IsSplitSelection (c : E ≃ₐ[F] E) (S : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ w ∈ S, conjPlace c w ≠ w ∧ conjPlace c w ∉ S

def unitAt (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) : (w.adicCompletion E)ˣ :=
  Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom x

theorem mem_unitsLevel_zero_of_valued_eq_one {w : HeightOneSpectrum (𝓞 E)}
    {x : (w.adicCompletion E)ˣ} (hx : Valued.v (x : w.adicCompletion E) = 1) :
    x ∈ unitsLevel (K := E) w 0 := by
  refine mem_unitsLevel.2 ⟨hx, ?_⟩
  calc Valued.v ((x : w.adicCompletion E) - 1)
      ≤ max (Valued.v (x : w.adicCompletion E)) (Valued.v (1 : w.adicCompletion E)) :=
        Valuation.map_sub _ _ _
    _ = _ := by simp [hx]

def negOneAt (w : HeightOneSpectrum (𝓞 E)) : unitsLevel (K := E) w 0 :=
  ⟨-1, mem_unitsLevel_zero_of_valued_eq_one (by simp)⟩

theorem unitAt_mem_of_pow_eq_one (w : HeightOneSpectrum (𝓞 E)) {ζ : Eˣ}
    (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) : unitAt w ζ ∈ unitsLevel (K := E) w 0 := by
  obtain ⟨n, hn, h⟩ := hζ
  apply mem_unitsLevel_zero_of_valued_eq_one
  have hζn : unitAt w ζ ^ n = 1 := by
    simp only [unitAt, ← map_pow, h, map_one]
  have hpow : Valued.v (unitAt w ζ : w.adicCompletion E) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hζn, Units.val_one, map_one]
  have h0 : Valued.v (unitAt w ζ : w.adicCompletion E) ≠ 0 := by simp
  rcases lt_trichotomy (Valued.v (unitAt w ζ : w.adicCompletion E)) 1 with hl | he | hg
  · exact absurd hpow (pow_lt_one₀ zero_le hl hn.ne').ne
  · exact he
  · exact absurd hpow (one_lt_pow₀ hg hn.ne').ne'

def rootAt (w : HeightOneSpectrum (𝓞 E)) {ζ : Eˣ} (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) :
    unitsLevel (K := E) w 0 :=
  ⟨unitAt w ζ, unitAt_mem_of_pow_eq_one w hζ⟩

variable (F) in

def IsSplitTypeCharacter (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ))
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (θ : (w : HeightOneSpectrum (𝓞 E)) → unitsLevel (K := E) w 0 →ₜ* Circle)
    (e : (E →+* ℂ) → ℤ) (μ : HeckeCharacter E) : Prop :=
  IsTrivialOnBase F μ ∧ (∀ τ ∈ Ψ, HasQuotientType μ τ (e τ)) ∧
    (∀ w, w ∉ S → conjPlace c w ∉ S → IsUnramifiedAt μ w) ∧
    ∀ w ∈ S, ∀ a : unitsLevel (K := E) w 0, μ.localComponent w a = θ w a

variable (F E) in

def UnramifiedAnticyclotomic : Set (HeckeCharacter E) :=
  {χ | IsTrivialOnBase F χ ∧ (∀ (w : InfinitePlace E) (z : (w.Completion)ˣ), χ.infiniteComponent w z = 1) ∧
    ∀ w, IsUnramifiedAt χ w}

end Objects

section Ties

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem extAt_coe (τ : E →+* ℂ) (x : WithAbs (InfinitePlace.mk τ).1) :
    extAt τ (x : (InfinitePlace.mk τ).Completion) = τ (WithAbs.equiv _ x) := by
  unfold extAt
  split_ifs with h
  · rw [Completion.extensionEmbedding_coe, h]
  · have h' := (embedding_mk_eq τ).resolve_left h
    rw [RingHom.comp_apply, Completion.extensionEmbedding_coe, h', ComplexEmbedding.conjugate_coe_eq]
    simp

omit [NumberField E] in

theorem extAt_surjective [IsTotallyComplex E] (τ : E →+* ℂ) : Function.Surjective (extAt τ) := by
  have hs := Completion.surjective_extensionEmbedding_of_isComplex
    (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
  unfold extAt
  split_ifs
  · exact hs
  · intro y
    obtain ⟨x, hx⟩ := hs (conj y)
    exact ⟨x, by simp [hx]⟩





omit [NumberField F] [NumberField E] in

theorem isSplitSelection_empty (c : E ≃ₐ[F] E) : IsSplitSelection c ∅ := by
  intro w hw
  simp at hw

variable (E) in

def embeddingImage : Finset (E →+* ℂ) :=
  open Classical in Finset.univ.image fun w : InfinitePlace E ↦ w.embedding



end Ties

section Statements

def SplitCharacterExistence.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ)),
    IsCMQuadratic F E → c ≠ 1 → IsUnramifiedAtFinitePlaces F E →
    RootsOfUnityArePlusMinusOne E → Even (Module.finrank ℚ F) → IsCMType Ψ →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))), IsSplitSelection c S →
    ∀ (θ : (w : HeightOneSpectrum (𝓞 E)) → unitsLevel (K := E) w 0 →ₜ* Circle),
      (∀ w ∈ S, ∃ n : ℕ, 0 < n ∧ ∀ a, θ w a ^ n = 1) →
    ∀ (e : (E →+* ℂ) → ℤ),
      (∃ μ : HeckeCharacter E, IsSplitTypeCharacter F c Ψ S θ e μ) ↔
        (-1 : ℂ) ^ (∑ τ ∈ Ψ, e τ) * ∏ w ∈ S, ((θ w (negOneAt w) : Circle) : ℂ) = 1

def SplitCharacterDifference.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ)),
    IsCMQuadratic F E → c ≠ 1 → IsUnramifiedAtFinitePlaces F E →
    RootsOfUnityArePlusMinusOne E → Even (Module.finrank ℚ F) → IsCMType Ψ →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))), IsSplitSelection c S →
    ∀ (θ : (w : HeightOneSpectrum (𝓞 E)) → unitsLevel (K := E) w 0 →ₜ* Circle),
      (∀ w ∈ S, ∃ n : ℕ, 0 < n ∧ ∀ a, θ w a ^ n = 1) →
    ∀ (e : (E →+* ℂ) → ℤ),
      (UnramifiedAnticyclotomic F E).Finite ∧
      ∀ μ₁ μ₂ : HeckeCharacter E, IsSplitTypeCharacter F c Ψ S θ e μ₁ →
        IsSplitTypeCharacter F c Ψ S θ e μ₂ → μ₁ / μ₂ ∈ UnramifiedAnticyclotomic F E

def SplitCharacterExistenceRoots.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ)),
    IsCMQuadratic F E → c ≠ 1 → IsUnramifiedAtFinitePlaces F E → IsCMType Ψ →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 E))), IsSplitSelection c S →
    ∀ (θ : (w : HeightOneSpectrum (𝓞 E)) → unitsLevel (K := E) w 0 →ₜ* Circle)
      (e : (E →+* ℂ) → ℤ),
      (∃ μ : HeckeCharacter E, IsSplitTypeCharacter F c Ψ S θ e μ) ↔
        ∀ (ζ : Eˣ) (hζ : ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1),
          (∏ τ ∈ Ψ, (τ (ζ : E)) ^ (-e τ)) * ∏ w ∈ S, ((θ w (rootAt w hζ) : Circle) : ℂ) = 1

def EtaTildeExistence.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ)) (η : HeckeCharacter F),
    IsCMQuadratic F E → c ≠ 1 → IsUnramifiedAtFinitePlaces F E →
    RootsOfUnityArePlusMinusOne E → Even (Module.finrank ℚ F) → IsCMType Ψ →
    IsQuadraticCharacterOf E η →
    ∀ (n : (E →+* ℂ) → ℤ), (∀ τ ∈ Ψ, Odd (n τ)) →
    ∀ (d : ℕ) (δ : 𝓞 E), 0 < d → δ ^ 2 = -(d : 𝓞 E) →
    ∀ (𝔞 : Ideal (𝓞 F)), Ideal.span {δ} = 𝔞.map (algebraMap (𝓞 F) (𝓞 E)) →
    ∀ (a : IdeleGroup F), IdeleGroup.toInfinite F a = 1 →
      ((IdeleGroup.toFractionalIdeal a : FractionalIdeal (𝓞 F)⁰ F) = (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) →
      ((∃ η' : HeckeCharacter E, (∀ w, IsUnramifiedAt η' w) ∧
          (∀ x : IdeleClassGroup F, η' (ideleClassMap F E x) = η x) ∧
          ∀ τ ∈ Ψ, HasAngularType η' τ (n τ)) ↔
        ((η (IdeleClassGroup.mk F a) : ℂ) *
          ∏ τ ∈ Ψ, (τ (δ : E) / (‖τ (δ : E)‖ : ℂ)) ^ n τ = 1))

def TameCharactersDistinct.Statement : Prop :=
  ∀ (g m : ℕ), g.Prime → 1 ≤ m → (4 * m * (g : ℝ) ^ ((1 : ℝ) / 4) < (g : ℝ) - 1) →
    ∀ ω : (ZMod g)ˣ →* ℂˣ, orderOf ω = g - 1 →
      (∀ k k' : ℤ, |k| ≤ m → |k'| ≤ m → ω ^ (2 * k) = ω ^ (2 * k') → k = k') ∧
      ∀ j : ℤ, (ω ^ (2 * j)) (-1) = 1

def FrameCharactersEven.Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (Ψ : Finset (E →+* ℂ)) (η : HeckeCharacter F),
    IsCMQuadratic F E → c ≠ 1 → IsUnramifiedAtFinitePlaces F E → IsCMType Ψ →
    IsQuadraticCharacterOf E η →
    ∀ (a a' : ℕ) (κ : (E →+* ℂ) → ℤ), Even a → Even a' →
      ((∃ α β : HeckeCharacter E, (∀ w, IsUnramifiedAt α w) ∧ (∀ w, IsUnramifiedAt β w) ∧
          (∀ x : IdeleClassGroup F, α (ideleClassMap F E x) = η x ^ a') ∧
          (∀ x : IdeleClassGroup F, β (ideleClassMap F E x) = η x ^ a) ∧
          ∀ τ ∈ Ψ, HasAngularType (α / β) τ (-κ τ)) ↔
        (∀ τ ∈ Ψ, Even (κ τ)) ∧
          ∀ ζ : Eˣ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → ∏ τ ∈ Ψ, (τ (ζ : E)) ^ (κ τ / 2) = 1)

end Statements

end GroundTheory.Heights₂.Theta
end
end
