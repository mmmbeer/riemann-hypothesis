import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SumThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CountSys
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntEqProdOfGaloisPermutedIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdicNormProdLeProdOfInjectiveClasses
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MapTraceEqSumRootsOfCharpolyMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowResDegPlaceNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdmissibleOfNewformAttached
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockConjugateRankThreeRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicCharacterRestrictCmFieldEqCyclotomicPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LevelTwistCyclotomicPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsIrrTwistAndRepIsoOfTwistRepIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SameSatTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterRealExponentEqZeroIffIsUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentUnitarisableTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.KlevThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.EventuallyNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IntK
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.KlevThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.EventuallyNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SignNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.TwCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ResTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.FrobEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNormVEqPrimePowLeFinrank
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleRankThreeStrengthen

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp
open scoped Matrix
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.V.Af.Bc
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

namespace UpperTheory.GalN.V.Win

structure EigData (n q : ℕ) (m : Fin n → ℤ) (wt : ℤ) where

  S : Type
  fin : Finite S

  β : S → Multiset ℂ
  card : ∀ s, (β s).card = n
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ e : S ≃ S, ∀ s, β (e s) = (β s).map σ
  pure : ∀ s, Win q wt (β s)
  int : ∀ a : ℤ, (∀ i, -a ≤ m i) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b)
  intInv : ∀ a : ℤ, (∀ i, m i ≤ a) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b⁻¹)

instance {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} : Inhabited (EigData n q m wt) :=
  ⟨⟨Empty, inferInstance, fun s => s.elim, fun s => s.elim, fun _ => ⟨.refl _, fun s => s.elim⟩, fun s => s.elim,
    fun _ _ s => s.elim, fun _ _ s => s.elim⟩⟩

def EigData.Classifies {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n q : ℕ}
    {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F))
    (admitted : (G F Ω →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, FrobEig ι r.1 w ((D.β (cl r)).map (·⁻¹))

def CountK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → (∀ i, m i + m i.rev = 1 - n) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m (1 - n), Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmK ι M m)

def CountP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmP ι M m)

def RootSum : Prop :=
  ∀ (n p : ℕ), 0 < p → ∀ (m : Fin n → ℤ) (wt : ℤ) (I : Type) [Fintype I] (q f : I → ℕ), (∀ i, 1 ≤ f i ∧ f i ≤ 2 ∧ q i = p ^ f i) →
    ∀ D : ∀ i, EigData n (q i) m wt, ∃ D' : EigData n p m wt, Nat.card D'.S ≤ 2 ^ (n + 1) * ∑ i, Nat.card (D i).S ∧
      ∃ e : (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) → D'.S,
        Function.Injective e ∧ ∀ x, D'.β (e x) = x.2.1.1.2

structure TrData (q e : ℕ) where

  S : Type
  fin : Finite S

  t : S → ℂ
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ u : S ≃ S, ∀ s, t (u s) = σ (t s)
  bd : ∀ s, ‖t s‖ ≤ Real.sqrt q + 2
  int : ∀ s, IsIntegral ℤ ((q : ℂ) ^ e * t s)

instance {q e : ℕ} : Inhabited (TrData q e) :=
  ⟨⟨Empty, inferInstance, fun s => s.elim, fun _ => ⟨.refl _, fun s => s.elim⟩, fun s => s.elim, fun s => s.elim⟩⟩

namespace TrData

variable {q e : ℕ}

def Classifies {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (D : TrData q e) (ι : Qbar l ≃+* ℂ) (g : Γ)
    (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, (r.1 g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace = ι.symm (D.t (cl r))

def sum (D D' : TrData q e) : TrData q e where
  S := D.S ⊕ D'.S
  fin := by have := D.fin; have := D'.fin; infer_instance
  t := Sum.elim D.t D'.t
  conj σ := by
    obtain ⟨u, hu⟩ := D.conj σ
    obtain ⟨u', hu'⟩ := D'.conj σ
    exact ⟨u.sumCongr u', fun s => by cases s <;> simp [hu, hu']⟩
  bd s := by cases s; exacts [D.bd _, D'.bd _]
  int s := by cases s; exacts [D.int _, D'.int _]

theorem card_sum (D D' : TrData q e) : Nat.card (D.sum D').S = Nat.card D.S + Nat.card D'.S := by
  have := D.fin; have := D'.fin
  exact Nat.card_sum

theorem Classifies.sum {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {D D' : TrData q e} {ι : Qbar l ≃+* ℂ} {g : Γ}
    {P P' : (Γ →* GL (Fin 3) (Qbar l)) → Prop} (h : D.Classifies ι g P) (h' : D'.Classifies ι g P') :
    (D.sum D').Classifies ι g fun r => P r ∨ P' r := by
  classical
  obtain ⟨cl, h1, h2⟩ := h
  obtain ⟨cl', h1', h2'⟩ := h'
  let F : {r // P r ∨ P' r} → D.S ⊕ D'.S :=
    fun r => if hr : P r.1 then Sum.inl (cl ⟨r.1, hr⟩) else Sum.inr (cl' ⟨r.1, r.2.resolve_left hr⟩)
  have e1 : ∀ r (hr : P r.1), F r = Sum.inl (cl ⟨r.1, hr⟩) := fun r hr => dif_pos hr
  have e2 : ∀ r (hr : ¬ P r.1), F r = Sum.inr (cl' ⟨r.1, r.2.resolve_left hr⟩) := fun r hr => dif_neg hr
  refine ⟨F, fun r r' (H : F r = F r') => ?_, fun r => ?_⟩
  · by_cases hr : P r.1 <;> by_cases hr' : P r'.1
    · rw [e1 r hr, e1 r' hr'] at H; exact h1 _ _ (Sum.inl.inj H)
    · rw [e1 r hr, e2 r' hr'] at H; cases H
    · rw [e2 r hr, e1 r' hr'] at H; cases H
    · rw [e2 r hr, e2 r' hr'] at H; exact h1' _ _ (Sum.inr.inj H)
  · change _ = ι.symm (Sum.elim D.t D'.t (F r))
    by_cases hr : P r.1
    · rw [e1 r hr]; exact h2 ⟨r.1, hr⟩
    · rw [e2 r hr]; exact h2' ⟨r.1, _⟩

end TrData

theorem exists_eigData {P W : Type} (Sig : Set P) (Iso : P → P → Prop) (sys : P → W → Multiset ℂ)
    (hiso : ∀ a ∈ Sig, ∀ b ∈ Sig, Iso a b → sys a = sys b) (N : ℕ)
    (hcard : ∀ S : Finset P, (∀ a ∈ S, a ∈ Sig) → (∀ a ∈ S, ∀ b ∈ S, Iso a b → a = b) → S.card ≤ N)
    (hconj : ∀ σ : ℂ ≃+* ℂ, ∀ a ∈ Sig, ∃ b ∈ Sig, ∀ v, sys b v = (sys a v).map σ)
    (w : W) {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (hn : ∀ a ∈ Sig, (sys a w).card = n)
    (hq : 0 < q) (hpure : ∀ a ∈ Sig, Win q (-(wt : ℝ)) (sys a w))
    (hint : ∀ a ∈ Sig, SlopesIn q m (sys a w)) :
    ∃ D : EigData n q m wt, Nat.card D.S ≤ N ∧ ∃ cl : ↥Sig → D.S, (∀ a b, cl a = cl b → sys a = sys b) ∧
      ∀ a, (D.β (cl a)).map (·⁻¹) = sys a w := by
  obtain ⟨hfin, hN⟩ := finite_image_of_card_le Sig Iso sys hiso N hcard
  refine ⟨⟨↥(sys '' Sig), hfin, fun s => (s.1 w).map (·⁻¹), ?_, ?_, ?_, ?_, ?_⟩, hN,
    fun a => ⟨sys a, a, a.2, rfl⟩, fun a b h => congrArg Subtype.val h, fun a => ?_⟩
  · rintro ⟨_, a, ha, rfl⟩
    simpa using hn a ha
  · intro σ
    have hmem : ∀ s : ↥(sys '' Sig), (fun v => (s.1 v).map σ) ∈ sys '' Sig := by
      rintro ⟨_, a, ha, rfl⟩
      obtain ⟨b, hb, h⟩ := hconj σ a ha
      exact ⟨b, hb, funext h⟩
    let F : ↥(sys '' Sig) → ↥(sys '' Sig) := fun s => ⟨_, hmem s⟩
    have hF : Function.Injective F := by
      intro s s' h
      refine Subtype.ext (funext fun v => ?_)
      exact Multiset.map_injective σ.injective (congrFun (congrArg Subtype.val h) v)
    refine ⟨Equiv.ofBijective F (Finite.injective_iff_bijective.1 hF), fun s => ?_⟩
    simp [F, Multiset.map_map]
  · rintro ⟨_, a, ha, rfl⟩
    exact (hpure a ha).inv hq
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    exact (hint a ha c hc).1 k hk
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [inv_inv]
    exact (hint a ha c hc).2 k hk
  · simp [Multiset.map_map]

end UpperTheory.GalN.V.Win
end
end

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

namespace UpperTheory.GalN.V.Win

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem add_add_le_add_two_of_mul_eq_one_of_sub_one_mul_nonneg (a u v w : ℝ) (ha : 1 ≤ a) (hw1 : 1 ≤ a * w) (hw2 : w ≤ a) (hw0 : 0 < w)
    (hp : u * v * w = 1) (huv : 0 ≤ (u - 1) * (v - 1)) : u + v + w ≤ a + 2 := by
  have h1 : 0 ≤ (a - w) * (a * w - 1) := mul_nonneg (by linarith) (by linarith)
  have h4 : a * (u * v * w) = a := by rw [hp, mul_one]
  have h5 : 0 ≤ (a - 1) * w := mul_nonneg (by linarith) hw0.le
  have h2 : w + u * v ≤ a + 1 := by
    have h3 : a * w * (w + u * v) ≤ a * w * (a + 1) := by nlinarith
    have : 0 < a * w := by positivity
    exact le_of_mul_le_mul_left h3 this
  nlinarith

private theorem add_add_le_add_two_of_mul_eq_one_of_one_le_mul_of_le (a y1 y2 y3 : ℝ) (ha : 1 ≤ a)
    (h11 : 1 ≤ a * y1) (h12 : y1 ≤ a) (h10 : 0 < y1)
    (h21 : 1 ≤ a * y2) (h22 : y2 ≤ a) (h20 : 0 < y2)
    (h31 : 1 ≤ a * y3) (h32 : y3 ≤ a) (h30 : 0 < y3)
    (hp : y1 * y2 * y3 = 1) : y1 + y2 + y3 ≤ a + 2 := by
  have c12 : 0 ≤ (y1 - 1) * (y2 - 1) → y1 + y2 + y3 ≤ a + 2 := fun h =>
    add_add_le_add_two_of_mul_eq_one_of_sub_one_mul_nonneg a y1 y2 y3 ha h31 h32 h30 hp h
  have c13 : 0 ≤ (y1 - 1) * (y3 - 1) → y1 + y2 + y3 ≤ a + 2 := fun h => by
    linarith [add_add_le_add_two_of_mul_eq_one_of_sub_one_mul_nonneg a y1 y3 y2 ha h21 h22 h20 (by rw [← hp]; ring) h]
  have c23 : 0 ≤ (y2 - 1) * (y3 - 1) → y1 + y2 + y3 ≤ a + 2 := fun h => by
    linarith [add_add_le_add_two_of_mul_eq_one_of_sub_one_mul_nonneg a y2 y3 y1 ha h11 h12 h10 (by rw [← hp]; ring) h]
  rcases le_total y1 1 with g1 | g1 <;> rcases le_total y2 1 with g2 | g2 <;>
    rcases le_total y3 1 with g3 | g3 <;>
    first
    | exact c12 (by nlinarith)
    | exact c13 (by nlinarith)
    | exact c23 (by nlinarith)

private theorem one_le_sqrt_mul_norm_inv_natCast_mul_and_le_sqrt_and_pos (q : ℕ) (hq : 1 ≤ q) (b : ℂ)
    (h1 : ((q : ℝ))⁻¹ < √(q : ℝ) * ‖b‖) (h2 : ‖b‖ < √(q : ℝ) * (q : ℝ)⁻¹) :
    1 ≤ √(q : ℝ) * ‖((q : ℂ) * b)⁻¹‖ ∧ ‖((q : ℂ) * b)⁻¹‖ ≤ √(q : ℝ) ∧ 0 < ‖((q : ℂ) * b)⁻¹‖ := by
  rw [norm_inv, norm_mul, Complex.norm_natCast]
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  have hs : 0 < √(q : ℝ) := Real.sqrt_pos.2 hQ0
  have hr : 0 < ‖b‖ := by
    by_contra hc
    push_neg at hc
    have : √(q : ℝ) * ‖b‖ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le hc
    have : (0 : ℝ) < (q : ℝ)⁻¹ := inv_pos.2 hQ0
    linarith
  have hQr : 0 < (q : ℝ) * ‖b‖ := mul_pos hQ0 hr
  have e1 : (q : ℝ) * ‖b‖ < √(q : ℝ) := by
    have := mul_lt_mul_of_pos_left h2 hQ0
    rwa [mul_left_comm, mul_inv_cancel₀ hQ0.ne', mul_one] at this
  have e2 : 1 < √(q : ℝ) * ((q : ℝ) * ‖b‖) := by
    have := mul_lt_mul_of_pos_left h1 hQ0
    rw [mul_inv_cancel₀ hQ0.ne'] at this
    linarith [show (q : ℝ) * (√(q : ℝ) * ‖b‖) = √(q : ℝ) * ((q : ℝ) * ‖b‖) by ring]
  refine ⟨?_, ?_, inv_pos.2 hQr⟩
  · rw [← div_eq_mul_inv, le_div_iff₀ hQr, one_mul]
    exact e1.le
  · rw [inv_le_iff_one_le_mul₀' hQr]
    linarith [show √(q : ℝ) * ((q : ℝ) * ‖b‖) = (q : ℝ) * ‖b‖ * √(q : ℝ) by ring]

theorem traces_from_eigenvalues_rank3 :
    ∀ (q e : ℕ), 1 ≤ q → ∀ D : EigData 3 q ![(e : ℤ) - 1, -1, -(e : ℤ) - 1] (1 - ((3 : ℕ) : ℤ)), ∃ (T : TrData q e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum := by
  intro q e hq D
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  refine ⟨⟨D.S, D.fin, fun s => ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum, ?_, ?_, ?_⟩,
    Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp [map_inv₀, map_mul, map_natCast]
  · intro s
    obtain ⟨b1, b2, b3, hb⟩ := Multiset.card_eq_three.1 (D.card s)
    have hw := D.pure s
    rw [hb] at hw
    unfold Win WinC at hw
    have hc : ((q : ℝ)) ^ ((((1 - ((3 : ℕ) : ℤ)) : ℤ) : ℝ) / 2) = (q : ℝ)⁻¹ := by
      norm_num [Real.rpow_neg_one]
    rw [hc] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have k1 := one_le_sqrt_mul_norm_inv_natCast_mul_and_le_sqrt_and_pos q hq b1 (hw1 b1 (by simp)).1 (hw1 b1 (by simp)).2
    have k2 := one_le_sqrt_mul_norm_inv_natCast_mul_and_le_sqrt_and_pos q hq b2 (hw1 b2 (by simp)).1 (hw1 b2 (by simp)).2
    have k3 := one_le_sqrt_mul_norm_inv_natCast_mul_and_le_sqrt_and_pos q hq b3 (hw1 b3 (by simp)).1 (hw1 b3 (by simp)).2
    have hQ0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hprod : ‖b1‖ * ‖b2‖ * ‖b3‖ = ((q : ℝ)⁻¹) ^ 3 := by
      simpa [norm_mul, mul_assoc] using hw2
    have hp : ‖((q : ℂ) * b1)⁻¹‖ * ‖((q : ℂ) * b2)⁻¹‖ * ‖((q : ℂ) * b3)⁻¹‖ = 1 := by
      simp only [norm_inv, norm_mul, Complex.norm_natCast]
      rw [← mul_inv, ← mul_inv, inv_eq_one]
      calc (q : ℝ) * ‖b1‖ * ((q : ℝ) * ‖b2‖) * ((q : ℝ) * ‖b3‖)
          = (q : ℝ) ^ 3 * (‖b1‖ * ‖b2‖ * ‖b3‖) := by ring
        _ = 1 := by rw [hprod, inv_pow, mul_inv_cancel₀ (pow_ne_zero 3 hQ0.ne')]
    have ha : 1 ≤ √(q : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hq)
    have key := add_add_le_add_two_of_mul_eq_one_of_one_le_mul_of_le (√(q : ℝ)) _ _ _ ha k1.1 k1.2.1 k1.2.2 k2.1 k2.2.1 k2.2.2
      k3.1 k3.2.1 k3.2.2 hp
    show ‖((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum‖ ≤ _
    rw [hb]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton]
    calc _ ≤ ‖((q : ℂ) * b1)⁻¹‖ + ‖((q : ℂ) * b2)⁻¹ + ((q : ℂ) * b3)⁻¹‖ := norm_add_le _ _
      _ ≤ ‖((q : ℂ) * b1)⁻¹‖ + (‖((q : ℂ) * b2)⁻¹‖ + ‖((q : ℂ) * b3)⁻¹‖) := by
          gcongr
          exact norm_add_le _ _
      _ ≤ _ := by linarith
  · intro s
    show IsIntegral ℤ ((q : ℂ) ^ e * ((D.β s).map fun b => ((q : ℂ) * b)⁻¹).sum)
    have hm : ∀ i : Fin 3, (![(e : ℤ) - 1, -1, -(e : ℤ) - 1] : Fin 3 → ℤ) i ≤ (e : ℤ) - 1 := by
      intro i
      fin_cases i <;> simp <;> omega
    have hb' : ∀ b ∈ D.β s, IsIntegral ℤ ((q : ℂ) ^ e * ((q : ℂ) * b)⁻¹) := by
      intro b hb
      have := D.intInv ((e : ℤ) - 1) hm s b hb
      have heq : (q : ℂ) ^ e * ((q : ℂ) * b)⁻¹ = (q : ℂ) ^ ((e : ℤ) - 1) * b⁻¹ := by
        rw [mul_inv, zpow_sub_one₀ hq0, zpow_natCast]
        ring
      rw [heq]
      exact this
    obtain ⟨b1, b2, b3, hb⟩ := Multiset.card_eq_three.1 (D.card s)
    have i1 := hb' b1 (by rw [hb]; simp)
    have i2 := hb' b2 (by rw [hb]; simp)
    have i3 := hb' b3 (by rw [hb]; simp)
    rw [hb]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton, mul_add]
    exact i1.add (i2.add i3)

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem norm_inv_pow_le_sqrt_and_pos_of_one_lt_sqrt_mul_norm (p : ℕ) (hp : 1 ≤ p) (h : ℕ) (b : ℂ)
    (h1 : 1 < √(p : ℝ) * ‖b‖) (h2 : ‖b‖ < √(p : ℝ) * 1) :
    ‖b⁻¹ ^ h‖ ≤ √((p ^ h : ℕ) : ℝ) ∧ 0 < ‖b⁻¹ ^ h‖ := by
  have hs : 0 < √(p : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < p by omega))
  have hr : 0 < ‖b‖ := by
    by_contra hc
    push_neg at hc
    have : √(p : ℝ) * ‖b‖ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le hc
    linarith
  have hsq : √((p ^ h : ℕ) : ℝ) = √(p : ℝ) ^ h := by
    rw [Nat.cast_pow, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
      Real.mul_self_sqrt (by positivity)]
  rw [hsq, norm_pow, norm_inv]
  refine ⟨pow_le_pow_left₀ (inv_nonneg.2 hr.le) ?_ h, pow_pos (inv_pos.2 hr) h⟩
  rw [inv_le_iff_one_le_mul₀' hr]
  linarith [show √(p : ℝ) * ‖b‖ = ‖b‖ * √(p : ℝ) by ring]

theorem traces_from_eigenvalues_rank2 :
    ∀ (p h e : ℕ), 1 ≤ p → ∀ D : EigData 2 p ![(e : ℤ), -(e : ℤ)] 0, ∃ (T : TrData (p ^ h) e) (u : D.S ≃ T.S), ∀ s, T.t (u s) = 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum := by
  intro p h e hp D
  refine ⟨⟨D.S, D.fin, fun s => 1 + ((D.β s).map fun b => b⁻¹ ^ h).sum, ?_, ?_, ?_⟩,
    Equiv.refl _, fun s => rfl⟩
  · intro σ
    obtain ⟨u, hu⟩ := D.conj σ
    refine ⟨u, fun s => ?_⟩
    rw [hu, map_add, map_one, map_multiset_sum, Multiset.map_map, Multiset.map_map]
    congr 2
    apply Multiset.map_congr rfl
    intro b _
    simp [map_inv₀, map_pow]
  · intro s
    obtain ⟨b1, b2, hb⟩ := Multiset.card_eq_two.1 (D.card s)
    have hw := D.pure s
    rw [hb] at hw
    unfold Win WinC at hw
    have hc : ((p : ℝ)) ^ ((((0 : ℤ)) : ℝ) / 2) = 1 := by simp
    rw [hc] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have k1 := norm_inv_pow_le_sqrt_and_pos_of_one_lt_sqrt_mul_norm p hp h b1 (by simpa using (hw1 b1 (by simp)).1) (hw1 b1 (by simp)).2
    have k2 := norm_inv_pow_le_sqrt_and_pos_of_one_lt_sqrt_mul_norm p hp h b2 (by simpa using (hw1 b2 (by simp)).1) (hw1 b2 (by simp)).2
    have hprod : ‖b1‖ * ‖b2‖ = 1 := by simpa [norm_mul] using hw2
    have hp2 : ‖b1⁻¹ ^ h‖ * ‖b2⁻¹ ^ h‖ = 1 := by
      rw [norm_pow, norm_pow, norm_inv, norm_inv, ← mul_pow, ← mul_inv, hprod, inv_one, one_pow]
    have ha : 1 ≤ √((p ^ h : ℕ) : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast Nat.one_le_pow _ _ (by omega))
    show ‖1 + ((D.β s).map fun b => b⁻¹ ^ h).sum‖ ≤ _
    rw [hb]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton]
    have hy : ‖b1⁻¹ ^ h‖ + ‖b2⁻¹ ^ h‖ ≤ √((p ^ h : ℕ) : ℝ) + 1 := by
      nlinarith [mul_nonneg (sub_nonneg.2 k1.1) (sub_nonneg.2 k2.1)]
    calc _ ≤ ‖(1 : ℂ)‖ + ‖b1⁻¹ ^ h + b2⁻¹ ^ h‖ := norm_add_le _ _
      _ ≤ ‖(1 : ℂ)‖ + (‖b1⁻¹ ^ h‖ + ‖b2⁻¹ ^ h‖) := by
          gcongr
          exact norm_add_le _ _
      _ ≤ _ := by rw [norm_one]; linarith
  · intro s
    show IsIntegral ℤ (((p ^ h : ℕ) : ℂ) ^ e * (1 + ((D.β s).map fun b => b⁻¹ ^ h).sum))
    have hm : ∀ i : Fin 2, (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i ≤ (e : ℤ) := by
      intro i
      fin_cases i <;> simp
    have hb' : ∀ b ∈ D.β s, IsIntegral ℤ (((p ^ h : ℕ) : ℂ) ^ e * b⁻¹ ^ h) := by
      intro b hb
      have := D.intInv (e : ℤ) hm s b hb
      rw [zpow_natCast] at this
      have heq : ((p ^ h : ℕ) : ℂ) ^ e * b⁻¹ ^ h = ((p : ℂ) ^ e * b⁻¹) ^ h := by
        rw [mul_pow, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm h e]
      rw [heq]
      exact this.pow h
    obtain ⟨b1, b2, hb⟩ := Multiset.card_eq_two.1 (D.card s)
    have i1 := hb' b1 (by rw [hb]; simp)
    have i2 := hb' b2 (by rw [hb]; simp)
    rw [hb]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton, mul_add, mul_one]
    have i0 : IsIntegral ℤ (((p ^ h : ℕ) : ℂ) ^ e) := by
      have : IsIntegral ℤ ((p ^ h : ℕ) : ℂ) := by
        simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((p ^ h : ℕ) : ℤ)))
      exact this.pow e
    exact i0.add (i1.add i2)

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem eisenstein_trace_difference_log_bound :
    ∀ (q e k : ℕ), 7 ≤ q → 1 ≤ e → 0 < k → ∀ z t : ℂ, z ^ k = 1 → ‖t‖ ≤ Real.sqrt q + 2 → IsIntegral ℤ ((q : ℂ) ^ e * t) → t ≠ eis3 q e z ∧ IsIntegral ℤ ((q : ℂ) ^ e * (t - eis3 q e z)) ∧ Real.log ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤ 2 * e * Real.log q + 1 := by
  intro q e k hq he hk z t hz ht hti
  have hQ : (7 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ0 : (0 : ℝ) < q := by linarith
  have hzn : ‖z‖ = 1 := by
    have h1 : ‖z‖ ^ k = 1 := by rw [← norm_pow, hz, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hk.ne').1 h1
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hzn
    norm_num at hzn
  have hzinv : z⁻¹ = z ^ (k - 1) :=
    (eq_inv_of_mul_eq_one_left (by rw [pow_sub_one_mul hk.ne', hz])).symm
  have hqc : ((q : ℂ) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show q ≠ 0 by omega))
  have hPc : ‖((q : ℂ) ^ e)‖ = (q : ℝ) ^ e := by rw [norm_pow, Complex.norm_natCast]
  have hQP : (q : ℝ) ≤ (q : ℝ) ^ e := le_self_pow₀ (by linarith) (by omega)
  have hP7 : (7 : ℝ) ≤ (q : ℝ) ^ e := le_trans hQ hQP
  have hs0 : 0 ≤ √(q : ℝ) := Real.sqrt_nonneg _
  have hs : √(q : ℝ) ≤ ((q : ℝ) + 9) / 6 := by
    nlinarith [Real.sq_sqrt hQ0.le, sq_nonneg (√(q : ℝ) - 3)]
  have hE : (q : ℂ) ^ e * (t - eis3 q e z) =
      (q : ℂ) ^ e * t - (z + (q : ℂ) ^ e + ((q : ℂ) ^ e) ^ 2 * z⁻¹) := by
    simp only [eis3]
    rw [mul_sub]
    congr 1
    rw [mul_add, mul_add, ← mul_assoc, mul_inv_cancel₀ hqc, one_mul, mul_one, ← mul_assoc, sq]
  have hne : t ≠ eis3 q e z := by
    intro heq
    have h1 : (q : ℂ) ^ e * z⁻¹ = eis3 q e z - ((((q : ℂ) ^ e)⁻¹ * z) + 1) := by
      simp only [eis3]; ring
    have h2 : ‖(q : ℂ) ^ e * z⁻¹‖ = (q : ℝ) ^ e := by
      rw [norm_mul, hPc, norm_inv, hzn, inv_one, mul_one]
    have h3 : ‖(((q : ℂ) ^ e)⁻¹ * z) + 1‖ ≤ ((q : ℝ) ^ e)⁻¹ + 1 := by
      calc _ ≤ ‖((q : ℂ) ^ e)⁻¹ * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul, norm_inv, hPc, hzn, mul_one, norm_one]
    have h4 : (q : ℝ) ^ e ≤ ‖eis3 q e z‖ + (((q : ℝ) ^ e)⁻¹ + 1) := by
      have h6 := norm_sub_le (eis3 q e z) ((((q : ℂ) ^ e)⁻¹ * z) + 1)
      rw [← h1, h2] at h6
      linarith
    have h5 : ((q : ℝ) ^ e)⁻¹ ≤ 1 / 7 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hP7
    rw [← heq] at h4
    linarith
  refine ⟨hne, ?_, ?_⟩
  · have hqi : IsIntegral ℤ ((q : ℂ) ^ e) := by
      have : IsIntegral ℤ (q : ℂ) := by
        simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ((q : ℕ) : ℤ)))
      exact this.pow e
    have hzi : IsIntegral ℤ z := IsIntegral.of_pow hk (by rw [hz]; exact isIntegral_one)
    have hzii : IsIntegral ℤ z⁻¹ := by rw [hzinv]; exact hzi.pow _
    rw [hE]
    exact hti.sub ((hzi.add hqi).add ((hqi.pow 2).mul hzii))
  · have hX0 : 0 < ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ :=
      norm_pos_iff.2 (mul_ne_zero hqc (sub_ne_zero.2 hne))
    rw [Real.log_le_iff_le_exp hX0]
    have hexp : Real.exp (2 * (e : ℝ) * Real.log q + 1) = ((q : ℝ) ^ e) ^ 2 * Real.exp 1 := by
      rw [Real.exp_add, show 2 * (e : ℝ) * Real.log q = ((2 * e : ℕ) : ℝ) * Real.log q by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log hQ0]
      ring
    rw [hexp]
    have hX : ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤
        (q : ℝ) ^ e * (√(q : ℝ) + 2) + (1 + (q : ℝ) ^ e + ((q : ℝ) ^ e) ^ 2) := by
      rw [hE]
      calc _ ≤ ‖(q : ℂ) ^ e * t‖ + ‖z + (q : ℂ) ^ e + ((q : ℂ) ^ e) ^ 2 * z⁻¹‖ := norm_sub_le _ _
        _ ≤ ‖(q : ℂ) ^ e * t‖ + (‖z‖ + ‖(q : ℂ) ^ e‖ + ‖((q : ℂ) ^ e) ^ 2 * z⁻¹‖) := by
            gcongr
            exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
        _ ≤ _ := by
            rw [norm_mul, hPc, hzn, norm_mul, norm_pow, hPc, norm_inv, hzn, inv_one, mul_one]
            gcongr
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hPs : 4 / 3 ≤ (q : ℝ) ^ e - √(q : ℝ) - 3 := by linarith
    have hP2 : (q : ℝ) ^ e * (√(q : ℝ) + 2) + (1 + (q : ℝ) ^ e + ((q : ℝ) ^ e) ^ 2)
        ≤ 2 * ((q : ℝ) ^ e) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hP7) (show (0 : ℝ) ≤ (q : ℝ) ^ e - √(q : ℝ) - 3 by linarith)]
    have hP0 : 0 ≤ ((q : ℝ) ^ e) ^ 2 := sq_nonneg _
    nlinarith

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem norm_natCast_qbar_eq_one_of_not_dvd (l q : ℕ) [Fact l.Prime] (h : ¬ l ∣ q) : ‖(q : Qbar l)‖ = 1 := by
  show ‖(q : PadicAlgCl l)‖ = 1
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
  have : ((q : ℚ_[l])) = ((q : ℚ) : ℚ_[l]) := by push_cast; rfl
  rw [this, Padic.eq_padicNorm]
  exact_mod_cast (padicNorm.nat_eq_one_iff q).2 h

theorem frobenius_trace_norm_nonzero_log_bound :
    ∀ (q e : ℕ), 7 ≤ q → 1 ≤ e → ∀ (D : TrData q e) (Orb : Type) [Fintype Orb] (z : Orb → ℂ), (∀ o, ∃ k : ℕ, 0 < k ∧ z o ^ k = 1) → (∀ σ : ℂ ≃+* ℂ, ∃ u : Orb ≃ Orb, ∀ o, z (u o) = σ (z o)) → ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ Fintype.card Orb * Nat.card D.S * (2 * e * Real.log q + 1) ∧ ∀ (l : ℕ) [Fact l.Prime], ¬ l ∣ q → ∀ (ι : Qbar l ≃+* ℂ) (Γ : Type) [Group Γ] (g : Γ) (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop), D.Classifies ι g admitted → ∀ X : Orb → Finset (Γ →* GL (Fin 3) (Qbar l)), (∀ o, ∀ ρ ∈ X o, admitted ρ) → (∀ o, ∀ ρ ∈ X o, ∀ ρ' ∈ X o, RepIso ρ ρ' → ρ = ρ') → (∀ o, ∀ ρ ∈ X o, (ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ ι.symm (eis3 q e (z o))) ∧ ‖((NN : ℤ) : Qbar l)‖ ≤ ∏ o, ∏ ρ ∈ X o, ‖(ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 q e (z o))‖ := by
  intro q e hq he D Orb _ z hz hσ
  haveI := D.fin
  haveI : Fintype D.S := Fintype.ofFinite _
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  let F : Orb → D.S → ℂ := fun o s => (q : ℂ) ^ e * (D.t s - eis3 q e (z o))
  have hF : ∀ o s, D.t s ≠ eis3 q e (z o) ∧ IsIntegral ℤ (F o s) ∧
      Real.log ‖F o s‖ ≤ 2 * e * Real.log q + 1 := by
    intro o s
    obtain ⟨k, hk, hzk⟩ := hz o
    exact eisenstein_trace_difference_log_bound q e k hq he hk (z o) (D.t s) hzk (D.bd s) (D.int s)
  have Heisenberg₂ : ∀ (σ : ℂ ≃+* ℂ) (w : ℂ), σ (eis3 q e w) = eis3 q e (σ w) := by
    intro σ w
    simp only [eis3]
    simp [map_add, map_mul, map_inv₀, map_pow, map_natCast]
  obtain ⟨NN, hNN⟩ := UpperTheory.exists_int_eq_prod_of_galois_permuted_integral (Orb × D.S) (fun x => F x.1 x.2) (fun x => (hF x.1 x.2).2.1) (by
    intro σ
    obtain ⟨uO, huO⟩ := hσ σ
    obtain ⟨uD, huD⟩ := D.conj σ
    refine ⟨Equiv.prodCongr uO uD, fun x => ?_⟩
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, F]
    rw [huO, huD, ← Heisenberg₂]
    simp [map_mul, map_sub, map_pow, map_natCast])
  have hprod : (NN : ℂ) = ∏ o, ∏ s, F o s := by rw [hNN, Fintype.prod_prod_type]
  have hne : ∀ o s, F o s ≠ 0 := fun o s =>
    mul_ne_zero (pow_ne_zero _ hq0) (sub_ne_zero.2 (hF o s).1)
  refine ⟨NN, ?_, ?_, ?_⟩
  · intro h0
    have h1 : (NN : ℂ) = 0 := by rw [h0]; simp
    rw [hprod] at h1
    obtain ⟨o, -, ho⟩ := Finset.prod_eq_zero_iff.1 h1
    obtain ⟨s, -, hs⟩ := Finset.prod_eq_zero_iff.1 ho
    exact hne o s hs
  · have habs : |(NN : ℝ)| = ∏ o, ∏ s, ‖F o s‖ := by
      rw [← Complex.norm_intCast, hprod, norm_prod]
      simp only [norm_prod]
    rw [habs, Real.log_prod (fun o _ => (Finset.prod_pos fun s _ => norm_pos_iff.2 (hne o s)).ne')]
    calc ∑ o, Real.log (∏ s, ‖F o s‖) = ∑ o, ∑ s, Real.log ‖F o s‖ := by
          apply Finset.sum_congr rfl
          intro o _
          exact Real.log_prod (fun s _ => (norm_pos_iff.2 (hne o s)).ne')
      _ ≤ ∑ o : Orb, ∑ s : D.S, (2 * (e : ℝ) * Real.log q + 1) :=
          Finset.sum_le_sum fun o _ => Finset.sum_le_sum fun s _ => (hF o s).2.2
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
          ring
  · intro l _ hlq ι Γ _ g admitted hcl X hAdm hX
    obtain ⟨cl, hcl1, hcl2⟩ := hcl
    have htr : ∀ o, ∀ ρ (hρ : ρ ∈ X o), (ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace =
        ι.symm (D.t (cl ⟨ρ, hAdm o ρ hρ⟩)) := fun o ρ hρ => hcl2 ⟨ρ, hAdm o ρ hρ⟩
    refine ⟨fun o ρ hρ => ?_, ?_⟩
    · rw [htr o ρ hρ]
      intro h
      exact (hF o _).1 (ι.symm.injective h)
    · let cl' : (o : Orb) → ↥(X o) → D.S := fun o r => cl ⟨r.1, hAdm o r.1 r.2⟩
      have hinj : ∀ o, Function.Injective (cl' o) := by
        intro o r r' h
        exact Subtype.ext (hX o r.1 r.2 r'.1 r'.2 (hcl1 _ _ h))
      have key := UpperTheory.adicNorm_prod_le_prod_of_injective_classes l ι Orb D.S (Γ →* GL (Fin 3) (Qbar l)) F (fun o s => (hF o s).2.1) X cl' hinj
      have hqn := norm_natCast_qbar_eq_one_of_not_dvd l q hlq
      have hL : ι.symm (∏ o, ∏ s, F o s) = ((NN : ℤ) : Qbar l) := by rw [← hprod, map_intCast]
      rw [hL] at key
      refine key.trans (le_of_eq ?_)
      apply Finset.prod_congr rfl
      intro o _
      refine Eq.trans ?_ (Finset.prod_coe_sort (X o)
        (fun ρ => ‖(ρ g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 q e (z o))‖))
      apply Finset.prod_congr rfl
      intro r _
      simp only [F, cl']
      rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, hqn, one_pow, one_mul, map_sub, htr o r.1 r.2]

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af



end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af



end

section

open UpperTheory.V.Af

section

end

private theorem rootSum_lemma (f : ℕ) (hf : 0 < f) (β B : Multiset ℂ)
    (h : Multiset.map (fun x => x ^ f) B = β) :
    B ∈ (Multiset.map (fun y => Polynomial.nthRoots f y) β).Sections := by
  subst h
  rw [Multiset.mem_sections, Multiset.map_map, Multiset.rel_map_left]
  apply Multiset.rel_refl_of_refl_on
  intro x _
  simp [Polynomial.mem_nthRoots hf]

private theorem card_sections_map_nthRoots_le_two_pow_of_le_two (f : ℕ) (hf2 : f ≤ 2) (β : Multiset ℂ) :
    ((Multiset.map (fun y => Polynomial.nthRoots f y) β).Sections).card ≤ 2 ^ β.card := by
  rw [Multiset.card_sections, Multiset.map_map]
  calc _ ≤ 2 ^ (Multiset.map (Multiset.card ∘ fun y => Polynomial.nthRoots f y) β).card :=
        Multiset.prod_le_pow_card _ _ (by
          intro x hx
          obtain ⟨y, _, rfl⟩ := Multiset.mem_map.1 hx
          exact (Polynomial.card_nthRoots f y).trans hf2)
    _ = _ := by rw [Multiset.card_map]

private theorem finite_and_card_map_pow_eq_le_two_pow_of_le_two (f : ℕ) (hf : 0 < f) (hf2 : f ≤ 2) (β : Multiset ℂ) :
    Finite {B : Multiset ℂ // Multiset.map (fun x => x ^ f) B = β} ∧
      Nat.card {B : Multiset ℂ // Multiset.map (fun x => x ^ f) B = β} ≤ 2 ^ β.card := by
  have hinj : Function.Injective (fun B : {B : Multiset ℂ // Multiset.map (fun x => x ^ f) B = β} =>
      (⟨B.1, Multiset.mem_toFinset.2 (rootSum_lemma f hf _ _ B.2)⟩ :
        ((Multiset.map (fun y => Polynomial.nthRoots f y) β).Sections.toFinset))) := by
    intro x y h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    exact h'
  refine ⟨Finite.of_injective _ hinj, ?_⟩
  calc _ ≤ Nat.card ((Multiset.map (fun y => Polynomial.nthRoots f y) β).Sections.toFinset) :=
        Nat.card_le_card_of_injective _ hinj
    _ = ((Multiset.map (fun y => Polynomial.nthRoots f y) β).Sections.toFinset).card :=
        Nat.card_eq_finsetCard _
    _ ≤ _ := (Multiset.toFinset_card_le _).trans (card_sections_map_nthRoots_le_two_pow_of_le_two f hf2 β)

private theorem win_of_map_pow_eq_of_win_pow (p f : ℕ) (hp : 0 < p) (hf : 0 < f) (wt : ℤ) (B β : Multiset ℂ)
    (h : Multiset.map (fun x => x ^ f) B = β) (hw : Win (p ^ f) (wt : ℝ) β) : Win p (wt : ℝ) B := by
  unfold Win WinC at *
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hc0 : 0 ≤ (p : ℝ) ^ ((wt : ℝ) / 2) := Real.rpow_nonneg hp0 _
  have hs0 : 0 ≤ √(p : ℝ) := Real.sqrt_nonneg _
  have h1 : ((p ^ f : ℕ) : ℝ) ^ ((wt : ℝ) / 2) = ((p : ℝ) ^ ((wt : ℝ) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) f, ← Real.rpow_mul hp0, mul_comm,
      Real.rpow_mul hp0, Real.rpow_natCast]
  have h2 : √((p ^ f : ℕ) : ℝ) = (√(p : ℝ)) ^ f := by
    rw [Nat.cast_pow, show (p : ℝ) ^ f = ((√(p : ℝ)) ^ f) ^ 2 by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hp0]]
    exact Real.sqrt_sq (pow_nonneg hs0 f)
  rw [h1, h2] at hw
  obtain ⟨hw1, hw2⟩ := hw
  subst h
  refine ⟨fun b hb => ?_, ?_⟩
  · have := hw1 (b ^ f) (Multiset.mem_map_of_mem _ hb)
    rw [norm_pow, ← mul_pow, ← mul_pow] at this
    exact ⟨(pow_lt_pow_iff_left₀ hc0 (mul_nonneg hs0 (norm_nonneg _)) hf.ne').1 this.1,
      (pow_lt_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hs0 hc0) hf.ne').1 this.2⟩
  · have hpr : (Multiset.map (fun x => x ^ f) B).prod = B.prod ^ f := by
      simpa using Multiset.prod_map_pow (m := B) (f := id) (n := f)
    rw [hpr, norm_pow, Multiset.card_map, ← pow_mul, mul_comm f, pow_mul] at hw2
    exact (pow_left_inj₀ (norm_nonneg _) (pow_nonneg hc0 _) hf.ne').1 hw2

private theorem isIntegral_zpow_mul_of_isIntegral_pow_zpow_mul_pow (p f : ℕ) (hf : 0 < f) (a : ℤ) (b : ℂ)
    (h : IsIntegral ℤ (((p ^ f : ℕ) : ℂ) ^ a * b ^ f)) : IsIntegral ℤ ((p : ℂ) ^ a * b) := by
  apply IsIntegral.of_pow hf
  have : ((p : ℂ) ^ a * b) ^ f = ((p ^ f : ℕ) : ℂ) ^ a * b ^ f := by
    rw [mul_pow, Nat.cast_pow, ← zpow_natCast ((p : ℂ) ^ a) f, ← zpow_natCast (p : ℂ) f,
      ← zpow_mul, ← zpow_mul, mul_comm a]
  rw [this]
  exact h

open UpperTheory.V.Br in
theorem rootSum :
    RootSum := by
  intro n p hp m wt I _ q f hf D
  have hf0 : ∀ i, 0 < f i := fun i => (hf i).1
  have key : ∀ (i : I) (σ : ℂ ≃+* ℂ) (B : Multiset ℂ),
      Multiset.map (fun x => x ^ f i) (Multiset.map σ B) =
        Multiset.map σ (Multiset.map (fun x => x ^ f i) B) := by
    intro i σ B
    simp [Multiset.map_map, Function.comp_def, map_pow]
  have hfib : ∀ i (s : (D i).S),
      Finite {B : Multiset ℂ // Multiset.map (fun x => x ^ f i) B = (D i).β s} ∧
        Nat.card {B : Multiset ℂ // Multiset.map (fun x => x ^ f i) B = (D i).β s} ≤ 2 ^ n := by
    intro i s
    have := finite_and_card_map_pow_eq_le_two_pow_of_le_two (f i) (hf0 i) (hf i).2.1 ((D i).β s)
    rwa [(D i).card s] at this
  have hT : ∀ i, Finite {x : (D i).S × Multiset ℂ // Multiset.map (fun x => x ^ f i) x.2 = (D i).β x.1} ∧
      Nat.card {x : (D i).S × Multiset ℂ // Multiset.map (fun x => x ^ f i) x.2 = (D i).β x.1}
        ≤ 2 ^ n * Nat.card (D i).S := by
    intro i
    haveI := (D i).fin
    haveI : Fintype (D i).S := Fintype.ofFinite _
    haveI : ∀ s, Finite {B : Multiset ℂ // Multiset.map (fun x => x ^ f i) B = (D i).β s} :=
      fun s => (hfib i s).1
    let E := Equiv.subtypeProdEquivSigmaSubtype
      (fun (s : (D i).S) (B : Multiset ℂ) => Multiset.map (fun x => x ^ f i) B = (D i).β s)
    refine ⟨Finite.of_equiv _ E.symm, ?_⟩
    rw [Nat.card_congr E, Nat.card_sigma]
    calc _ ≤ ∑ _s : (D i).S, 2 ^ n := Finset.sum_le_sum fun s _ => (hfib i s).2
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, mul_comm]
  haveI : ∀ i, Finite {x : (D i).S × Multiset ℂ // Multiset.map (fun x => x ^ f i) x.2 = (D i).β x.1} :=
    fun i => (hT i).1
  refine ⟨⟨(i : I) × {x : (D i).S × Multiset ℂ // Multiset.map (fun x => x ^ f i) x.2 = (D i).β x.1} × Bool,
      inferInstance, fun x => x.2.1.1.2, ?_, ?_, ?_, ?_, ?_⟩, ?_, id, Function.injective_id, fun _ => rfl⟩
  · intro x
    have := congrArg Multiset.card x.2.1.2
    simpa [(D x.1).card] using this
  · intro σ
    choose e he using fun i => (D i).conj σ
    let mE : Multiset ℂ ≃ Multiset ℂ :=
      ⟨Multiset.map σ, Multiset.map σ.symm, fun B => by simp [Multiset.map_map, Function.comp_def],
        fun B => by simp [Multiset.map_map, Function.comp_def]⟩
    refine ⟨Equiv.sigmaCongrRight fun i => Equiv.prodCongr (Equiv.subtypeEquiv
      (Equiv.prodCongr (e i) mE) (fun x => ?_)) (Equiv.refl Bool), fun x => rfl⟩
    rcases x with ⟨s, B⟩
    show _ ↔ Multiset.map (fun y => y ^ f i) (Multiset.map σ B) = (D i).β (e i s)
    rw [he, key]
    exact (Multiset.map_injective σ.injective).eq_iff.symm
  · intro x
    exact win_of_map_pow_eq_of_win_pow p (f x.1) hp (hf0 x.1) wt _ _ x.2.1.2
      (by rw [← (hf x.1).2.2]; exact (D x.1).pure x.2.1.1.1)
  · intro a ha x b hb
    have hm : b ^ f x.1 ∈ (D x.1).β x.2.1.1.1 := x.2.1.2 ▸ Multiset.mem_map_of_mem _ hb
    exact isIntegral_zpow_mul_of_isIntegral_pow_zpow_mul_pow p (f x.1) (hf0 x.1) a b
      (by rw [← (hf x.1).2.2]; exact (D x.1).int a ha _ _ hm)
  · intro a ha x b hb
    have hm : b ^ f x.1 ∈ (D x.1).β x.2.1.1.1 := x.2.1.2 ▸ Multiset.mem_map_of_mem _ hb
    have := (D x.1).intInv a ha _ _ hm
    rw [← inv_pow] at this
    exact isIntegral_zpow_mul_of_isIntegral_pow_zpow_mul_pow p (f x.1) (hf0 x.1) a b⁻¹
      (by rw [← (hf x.1).2.2]; exact this)
  · rw [Nat.card_sigma, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    calc _ ≤ (2 ^ n * Nat.card (D i).S) * 2 := Nat.mul_le_mul_right 2 (hT i).2
      _ = 2 ^ (n + 1) * Nat.card (D i).S := by ring

end

end UpperTheory.GalN.V.Win
end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.HeckeGal.Model UpperTheory.V.Af

namespace UpperTheory.GalN.V

variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ}

theorem winC_of_unitary {π : CG K n} (hu : π.IsUnitary) {w : HeightOneSpectrum (𝓞 K)} {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    WinC 1 (Real.sqrt (normV w)) (B.map fun b : ℂˣ => (b : ℂ)) := by
  have hq : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hq1 : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℕ) := by
    exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w)
  refine ⟨fun b hb => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    obtain ⟨h1, h2⟩ := PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound K n π hu w B hB a ha
    rw [hq, Real.sqrt_eq_rpow, mul_one]
    refine ⟨?_, h2⟩
    rw [Real.rpow_neg hq1.le, inv_lt_iff_one_lt_mul₀' (Real.rpow_pos_of_pos hq1 _)] at h1
    exact h1
  · induction π using Quotient.inductionOn with | _ π =>
    obtain ⟨ω, hω1, hω⟩ := hu
    have e := PositivityTheory.jumpWindows.PSmo.val_eq_prod (π := π) hω hB
    rw [one_pow, show (B.map fun b : ℂˣ => (b : ℂ)).prod = ((B.prod : ℂˣ) : ℂ) from (map_multiset_prod (Units.coeHom ℂ) B).symm, ← e]
    exact hω1 _

theorem unitary_twist (hn : 1 ≤ n) (π : CuspSub K n) (t : ℝ) (m : Multiset ℂ) (hm : ∀ τ, π.HasInfChar τ m)
    (hc : m.card = n) (ht : m.sum = (n : ℂ) * t) : (CG.mk (π.twist (absPow K (-t)))).IsUnitary := by
  obtain ⟨h1, h2⟩ := GlobalTheory.ResW.rexp_eq_zero_iff_isUnitary K ⟨n, π.twist (absPow K (-t))⟩ hn
  refine h2.1 (h1.1 ?_)
  rw [GlobalTheory.ResW.rexp, GlobalTheory.UnitLocWeight.cex_eq, Finset.sum_eq_zero]
  · simp
  intro τ _
  have k := (hm τ).twist (absPow K (-t))
  rw [(InfType.expo_of_infType K _).2.1 (-t) (absPow_isAbsPow K (-t)) τ] at k
  rw [CG.HasInfChar.infChar_eq (π := CG.mk _) k, Multiset.sum_map_add, Multiset.map_id', Multiset.map_const',
    Multiset.sum_replicate, hc, ht, nsmul_eq_mul]
  push_cast; ring

theorem win_algSat (hn : 1 ≤ n) (π : CuspSub K n) (m : Fin n → ℤ) (wt : ℤ) (hwt : ∀ i, m i + m i.rev = wt)
    (hm : ∀ τ, π.HasInfChar τ (infOf m)) {w : HeightOneSpectrum (𝓞 K)} {B : Multiset ℂˣ} (hB : (CG.mk π).HasSat w B) :
    Win (normV w) (-(wt : ℝ)) (algSat n (normV w) B) := by
  have hq : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hq1 : (0 : ℝ) < (normV w : ℕ) := by
    rw [hq]; exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w)
  set t : ℝ := ((n : ℝ) - 1 + wt) / 2 with ht
  have hs : (infOf m).sum = (n : ℂ) * t := by
    have s2 : ∑ i : Fin n, (m i + m i.rev) = ∑ _i : Fin n, wt := Finset.sum_congr rfl fun i _ => hwt i
    have s3 : ∑ i : Fin n, m i.rev = ∑ i, m i := Equiv.sum_comp Fin.revPerm m
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, s3] at s2
    have s4 : (∑ i, (m i : ℂ)) + ∑ i, (m i : ℂ) = n * wt := by exact_mod_cast s2
    change ∑ i : Fin n, (((n : ℂ) - 1) / 2 + (m i : ℂ)) = _
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ht]
    push_cast
    linear_combination s4 / 2
  obtain ⟨h1, h2⟩ := CG.HasSat.twist_absPow hB (-t)
  have W0 := winC_of_unitary (unitary_twist hn π t _ hm (by simp [infOf]) hs) h1
  set ν : ℂˣ := (absPow K (-t)).val w
  have W1 := W0.map_mul (u := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (ν : ℂ)⁻¹)
    (mul_ne_zero (by exact_mod_cast (Real.rpow_pos_of_pos hq1 _).ne') (inv_ne_zero ν.ne_zero))
  rw [norm_mul, norm_inv, h2, ← hq, Complex.norm_real, Real.norm_of_nonneg (by positivity), neg_neg, ← Real.rpow_neg hq1.le,
    ← Real.rpow_add hq1, mul_one] at W1
  unfold Win
  convert W1 using 2
  · rw [ht]; ring
  · simp only [algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, Units.val_mul]
    field_simp

end UpperTheory.GalN.V
end

section
noncomputable section

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

namespace UpperTheory.GalN.V.Win.N

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp
open scoped Matrix
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.V.Af.Bc
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

def CountK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → (∀ i, m i + m i.rev = 1 - n) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m (1 - n), Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmKN ι M m)

def CountP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmPN ι M m)

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.CuspRep UpperTheory.V.Af in
theorem countK :
    UpperTheory.V.Af.Hypotheses₂ → LevelKN → CountK := by
  intro hP hL K _ _ _ n hn
  classical
  obtain ⟨c, A, hcard⟩ := cardK hP K n hn
  refine ⟨c, A, fun m hm hwt H hH M hM p w hp hw hpM hpd => ?_⟩
  have hwM : (M : 𝓞 K) ∉ w.asIdeal := natCast_notMem_of_not_dvd hp hw hpM
  let Wd := {v : HeightOneSpectrum (𝓞 K) // (M : 𝓞 K) ∉ v.asIdeal}
  let sys : CuspSub K n → Wd → Multiset ℂ := fun π v =>
    if h : ∃ B, (CG.mk π).HasSat v.1 B then algSat n (normV v.1) h.choose else 0
  have hsys : ∀ π (v : Wd) B, (CG.mk π).HasSat v.1 B → sys π v = algSat n (normV v.1) B := by
    intro π v B hB
    have h : ∃ B, (CG.mk π).HasSat v.1 B := ⟨B, hB⟩
    simp only [sys, dif_pos h]
    rw [h.choose_spec.unique hB]
  have hsat : ∀ π ∈ SigK K m M, ∀ v : Wd, ∃ B, (CG.mk π).HasSat v.1 B := fun π hπ v =>
    satK hP K n M π hπ.2.2 v.1 v.2
  obtain ⟨D, hD, cl, hcl, hβ⟩ := exists_eigData (SigK K m M) (fun π π' => π.Iso π') sys
    (fun π hπ π' _ h => funext fun v => by
      obtain ⟨B, hB⟩ := hsat π hπ v
      rw [hsys π v B hB, hsys π' v B (CuspSub.Iso.hasSatGL h hB)])
    (c * (M * (H + 1)) ^ A) (hcard m hm H hH M hM)
    (fun σ π hπ => by
      obtain ⟨π', hπ', h⟩ := conjK hP K n hn m hm M hM σ π hπ
      refine ⟨π', hπ', fun v => ?_⟩
      obtain ⟨B, hB⟩ := hsat π hπ v
      obtain ⟨B', hB', e⟩ := h v.1 B hB
      rw [hsys π v B hB, hsys π' v B' hB', e])
    ⟨w, hwM⟩ (n := n) (q := normV w) (m := m) (wt := 1 - n)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB, algSat, Multiset.card_map, ← hB.card]
      simp)
    (by exact zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact win_algSat (by omega) π m _ hwt hπ.1 hB)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact intK hP K n hn m hm M hM π hπ p w hp hw hpM hpd B hB)
  refine ⟨D, hD, fun l hl hl2 hlp Ω _ _ _ ι => ?_⟩
  have hform : ∀ r : {r : G K Ω →* GL (Fin n) (Qbar l) // AdmKN ι M m r}, ∃ π : ↥(SigK K m M), IsSSRep r.1 ∧
      ∀ v : Wd, (l : 𝓞 K) ∉ v.1.asIdeal → FrobEig ι r.1 v.1 (sys π v) := by
    intro r
    obtain ⟨π, h1, h2, h3⟩ := r.2.aut.1
    obtain ⟨hπ, hF⟩ := hL K n hn m hm M hM l hl2 Ω ι r.1 π r.2.level r.2.odd (r.2.aut.2 r.2.level.cont) h1 h2 h3
    refine ⟨⟨π, hπ⟩, h3.1, fun v hv => ?_⟩
    obtain ⟨B, hB⟩ := hsat π hπ v
    rw [hsys π v B hB]
    exact hF v.1 hv B hB
  choose f hss hf using hform
  refine ⟨fun r => cl (f r), fun r r' h => ?_, fun r => ?_⟩
  · refine isoOfFrob hP K Ω l ι n r.1 r'.1 r.2.level.cont r'.2.level.cont (hss r) (hss r') ?_
    filter_upwards [eventually_natCast_notMem (F := K) (M := M) (by omega),
      eventually_natCast_notMem (F := K) hl.out.ne_zero] with v hvM hvl
    refine ⟨sys (f r) ⟨v, hvM⟩, hf r ⟨v, hvM⟩ hvl, ?_⟩
    rw [hcl _ _ h]
    exact hf r' ⟨v, hvM⟩ hvl
  · rw [hβ]
    refine hf r ⟨w, hwM⟩ (natCast_notMem_of_not_dvd hp hw fun h => hlp ?_)
    exact ((Nat.prime_dvd_prime_iff_eq hp hl.out).1 h).symm

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.CuspRep UpperTheory.V.Af in
theorem countP :
    UpperTheory.V.Af.Hypotheses₂ → LevelPN → CountP := by
  intro hP hL K _ _ _ hK n hn
  classical
  obtain ⟨c, A, hcard⟩ := cardP hP K n hn
  refine ⟨c, A, fun m wt hm hwt H hH M hM p w hp hw hpM hpd => ?_⟩
  have hwM : (M : 𝓞 K) ∉ w.asIdeal := natCast_notMem_of_not_dvd hp hw hpM
  let Wd := {v : HeightOneSpectrum (𝓞 K) // (M : 𝓞 K) ∉ v.asIdeal}
  let sys : CuspSub K n → Wd → Multiset ℂ := fun π v =>
    if h : ∃ B, (CG.mk π).HasSat v.1 B then algSat n (normV v.1) h.choose else 0
  have hsys : ∀ π (v : Wd) B, (CG.mk π).HasSat v.1 B → sys π v = algSat n (normV v.1) B := by
    intro π v B hB
    have h : ∃ B, (CG.mk π).HasSat v.1 B := ⟨B, hB⟩
    simp only [sys, dif_pos h]
    rw [h.choose_spec.unique hB]
  have hsat : ∀ π ∈ SigP K m M, ∀ v : Wd, ∃ B, (CG.mk π).HasSat v.1 B := fun π hπ v =>
    satK hP K n M π hπ.2.2 v.1 v.2
  obtain ⟨D, hD, cl, hcl, hβ⟩ := exists_eigData (SigP K m M) (fun π π' => π.Iso π') sys
    (fun π hπ π' _ h => funext fun v => by
      obtain ⟨B, hB⟩ := hsat π hπ v
      rw [hsys π v B hB, hsys π' v B (CuspSub.Iso.hasSatGL h hB)])
    (c * (M * (H + 1)) ^ A) (hcard m hm H hH M hM)
    (fun σ π hπ => by
      obtain ⟨π', hπ', h⟩ := conjPrime₂ hP K hK n hn m hm M hM σ π hπ
      refine ⟨π', hπ', fun v => ?_⟩
      obtain ⟨B, hB⟩ := hsat π hπ v
      obtain ⟨B', hB', e⟩ := h v.1 B hB
      rw [hsys π v B hB, hsys π' v B' hB', e])
    ⟨w, hwM⟩ (n := n) (q := normV w) (m := m) (wt := wt)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB, algSat, Multiset.card_map, ← hB.card]
      simp)
    (by exact zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w))
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact win_algSat (by omega) π m _ hwt hπ.1 hB)
    (fun π hπ => by
      obtain ⟨B, hB⟩ := hsat π hπ ⟨w, hwM⟩
      rw [hsys π _ B hB]
      exact intP hP K n hn m hm M hM π hπ p w hp hw hpM hpd B hB)
  refine ⟨D, hD, fun l hl hl2 hlp Ω _ _ _ ι => ?_⟩
  have hform : ∀ r : {r : G K Ω →* GL (Fin n) (Qbar l) // AdmPN ι M m r}, ∃ π : ↥(SigP K m M), IsSSRep r.1 ∧
      ∀ v : Wd, (l : 𝓞 K) ∉ v.1.asIdeal → FrobEig ι r.1 v.1 (sys π v) := by
    intro r
    obtain ⟨π, h1, h2, h3⟩ := r.2.aut
    obtain ⟨hπ, hF⟩ := hL K hK n hn m hm M hM l hl2 Ω ι r.1 π r.2.level r.2.safe r.2.unl h1 h2 h3
    refine ⟨⟨π, hπ⟩, h3.1, fun v hv => ?_⟩
    obtain ⟨B, hB⟩ := hsat π hπ v
    rw [hsys π v B hB]
    exact hF v.1 hv B hB
  choose f hss hf using hform
  refine ⟨fun r => cl (f r), fun r r' h => ?_, fun r => ?_⟩
  · refine isoOfFrob hP K Ω l ι n r.1 r'.1 r.2.level.cont r'.2.level.cont (hss r) (hss r') ?_
    filter_upwards [eventually_natCast_notMem (F := K) (M := M) (by omega),
      eventually_natCast_notMem (F := K) hl.out.ne_zero] with v hvM hvl
    refine ⟨sys (f r) ⟨v, hvM⟩, hf r ⟨v, hvM⟩ hvl, ?_⟩
    rw [hcl _ _ h]
    exact hf r' ⟨v, hvM⟩ hvl
  · rw [hβ]
    refine hf r ⟨w, hwM⟩ (natCast_notMem_of_not_dvd hp hw fun h => hlp ?_)
    exact ((Nat.prime_dvd_prime_iff_eq hp hl.out).1 h).symm

end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
  UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Br

private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  obtain ⟨h, h1, h2, h3⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank ℚ p w hp hw
  rw [Module.finrank_self] at h2
  rw [h3, le_antisymm h2 h1, pow_one]

private theorem exists_over (K : Type) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (f : ℕ), v.under (𝓞 ℚ) = w ∧ (p : 𝓞 K) ∈ v.asIdeal ∧ 1 ≤ f ∧ f ≤ 2 ∧ normV v = p ^ f := by
  haveI := w.isMaximal
  obtain ⟨Q, hQ, hL⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) w.asIdeal
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have : (p : 𝓞 ℚ) ∈ Q.under (𝓞 ℚ) := hL.over ▸ hw
    simpa [Ideal.under, Ideal.mem_comap] using this
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by simpa using hpQ)
  obtain ⟨f, f1, f2, f3⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank K p ⟨Q, hQ.isPrime, h0⟩ hp hpQ
  exact ⟨⟨Q, hQ.isPrime, h0⟩, f, HeightOneSpectrum.ext hL.over.symm, hpQ, f1, h2 ▸ f2, f3⟩

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem place_over_rational_prime (K : Type) [Field K] [NumberField K] (p : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (hw : (p : 𝓞 K) ∈ w.asIdeal) : ∃ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal := by
  refine ⟨w.under (𝓞 ℚ), ?_⟩
  change (p : 𝓞 ℚ) ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K))
  rw [Ideal.mem_comap, map_natCast]
  exact hw

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

end

end UpperTheory.GalN.V.Win.N
end
end
