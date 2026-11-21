import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.StatementsGluing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Antisym

open MvPolynomial

section Antisymmetric

abbrev Poly (T : Type) (N : ℕ) := MvPolynomial (T × Fin N) ℝ

def SameBlock {N : ℕ} (j : ℕ) (a b : Fin N) : Prop := (a.val < j ↔ b.val < j)

def IsLeviPerm {T : Type} {N : ℕ} (j : ℕ) (w : Equiv.Perm (T × Fin N)) : Prop :=
  ∀ τ i, (w (τ, i)).1 = τ ∧ SameBlock j (w (τ, i)).2 i

def IsSimpleTransp {T : Type} [DecidableEq T] {N : ℕ} (j : ℕ) (s : Equiv.Perm (T × Fin N)) : Prop :=
  ∃ (τ : T) (a b : Fin N), b.val = a.val + 1 ∧ SameBlock j a b ∧ s = Equiv.swap (τ, a) (τ, b)

def delta (T : Type) [Fintype T] (N : ℕ) : Poly T N :=
  ∏ τ : T, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, (X (τ, a) - X (τ, b))

def deltaDeg (T : Type) [Fintype T] (N : ℕ) : ℕ := Fintype.card T * (N * (N - 1) / 2)

def antiSpace (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) : Set (Poly T N) :=
  {P | P.IsHomogeneous (deltaDeg T N + 1) ∧
    ∀ s : Equiv.Perm (T × Fin N), IsSimpleTransp j s → rename s P = -P}

def invForms (T : Type) (N j : ℕ) : Set (Poly T N) :=
  {l | l.IsHomogeneous 1 ∧ ∀ w : Equiv.Perm (T × Fin N), IsLeviPerm j w → rename w l = l}

def IsCross {N : ℕ} (j : ℕ) (a b : Fin N) : Prop := a.val < j ∧ j ≤ b.val

def hyperplane {T : Type} {N : ℕ} (τ : T) (a b : Fin N) : Set (T × Fin N → ℝ) :=
  {x | x (τ, a) = x (τ, b)}

def HasRelInterior {T : Type} [Fintype T] {N : ℕ} (H S : Set (T × Fin N → ℝ)) : Prop :=
  ∃ p ∈ S, ∃ ε > 0, H ∩ Metric.ball p ε ⊆ S

def supAbs {T : Type} {N : ℕ} (S : Set (T × Fin N → ℝ)) (P : Poly T N) : ℝ :=
  sSup ((fun x => |eval x P|) '' S)

def crossUnion {T : Type} {N : ℕ} (j : ℕ) (Om : T → Fin N → Fin N → Set (T × Fin N → ℝ)) :
    Set (T × Fin N → ℝ) :=
  ⋃ (τ : T) (a : Fin N) (b : Fin N) (_ : IsCross j a b), Om τ a b

def IsCrossFamily {T : Type} [Fintype T] {N : ℕ} (j : ℕ) (Om : T → Fin N → Fin N → Set (T × Fin N → ℝ)) : Prop :=
  ∀ τ a b, IsCross j a b → Om τ a b ⊆ hyperplane τ a b ∧ IsCompact (Om τ a b) ∧
    HasRelInterior (hyperplane τ a b) (Om τ a b)

def adjHyperplane {T : Type} {N : ℕ} (j : ℕ) (hj : 0 < j) (hjN : j < N) (τ : T) :
    Set (T × Fin N → ℝ) :=
  hyperplane τ ⟨j - 1, by omega⟩ ⟨j, hjN⟩

def IsAdjFamily {T : Type} [Fintype T] {N : ℕ} (j : ℕ) (hj : 0 < j) (hjN : j < N) (h : Poly T N)
    (K : T → Set (T × Fin N → ℝ)) : Prop :=
  ∀ τ, K τ ⊆ adjHyperplane j hj hjN τ ∧ IsCompact (K τ) ∧
    HasRelInterior (adjHyperplane j hj hjN τ) (K τ) ∧ ∀ x ∈ K τ, eval x h = 0

def AntisymDivisible.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (P : Poly T N),
    P ∈ antiSpace T N j →
    (∀ (τ : T) (a b : Fin N), IsCross j a b →
      ∃ U ⊆ hyperplane τ a b, HasRelInterior (hyperplane τ a b) U ∧ ∀ x ∈ U, eval x P = 0) →
    ∃ l ∈ invForms T N j, P = delta T N * l

def AntisymStable.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ)
    (Om : T → Fin N → Fin N → Set (T × Fin N → ℝ)), IsCrossFamily j Om →
    ∃ C : ℝ, ∀ P ∈ antiSpace T N j, ∃ l ∈ invForms T N j,
      ∀ m, |coeff m (P - delta T N * l)| ≤ C * supAbs (crossUnion j Om) P

def AntisymPerturbed.Statement : Prop :=
  ∀ (T : Type) [Fintype T] [DecidableEq T] (N j : ℕ) (hj : 0 < j) (hjN : j < N) (h : Poly T N)
    (K : T → Set (T × Fin N → ℝ)), IsAdjFamily j hj hjN h K →
    ∃ C : ℝ, ∀ (P : Poly T N) (v ε : ℝ), P - v • h ∈ antiSpace T N j →
      (∀ τ, ∀ x ∈ K τ, |eval x P| ≤ ε) →
      ∃ l ∈ invForms T N j, ∀ m, |coeff m (P - v • h - delta T N * l)| ≤ C * ε

end Antisymmetric

section Gluing

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing segreJoin NefOnFibres mCoordIdeal)
open TensorProduct

variable {Ω : Type} [Field Ω]

def locPrimeTo (A : Subalgebra ℤ Ω) (p : ℕ) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ ((A : Set Ω) ∪ {u | ∃ s : ℕ, ¬ p ∣ s ∧ u = (s : Ω)⁻¹})

def invertNat (A : Subalgebra ℤ Ω) (m : ℕ) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ ((A : Set Ω) ∪ {(m : Ω)⁻¹})

def IsLocFreeLattice {E : Type} [AddCommGroup E] [Module Ω E] (B : Subalgebra ℤ Ω) (r : ℕ)
    (L : AddSubgroup E) : Prop :=
  (∀ a ∈ B, ∀ e ∈ L, a • e ∈ L) ∧
  ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ B) ∧ (∀ l, c l ∈ B) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ L) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ B) ∧ e = ∑ q, a q • b q

def LocallyFreeSpread.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ι : Type) [Fintype ι] (x : ι → Ω) (c : ι) (p r : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (L : AddSubgroup E),
    p.Prime → x c ≠ 0 → IsLocFreeLattice (locPrimeTo (chartRing ℤ x c) p) r L →
    ∃ m : ℕ, ¬ p ∣ m ∧ ∃ L' : AddSubgroup E, IsLocFreeLattice (invertNat (chartRing ℤ x c) m) r L' ∧
      ∀ e, e ∈ L ↔ ∃ s : ℕ, ¬ p ∣ s ∧ (s : Ω) • e ∈ L'

def pullLat {Ω' : Type} [Field Ω'] [Algebra Ω Ω'] {ι κ : Type} {E : Type} [AddCommGroup E]
    [Module Ω E] (x : ι → Ω) (z : κ → Ω') (L : ι → AddSubgroup E) (q : ι × κ) :
    AddSubgroup (Ω' ⊗[Ω] E) :=
  AddSubgroup.closure {v | ∃ a ∈ chartRing ℤ (segreJoin (fun i => algebraMap Ω Ω' (x i)) z) q,
    ∃ e ∈ L q.1, v = a • ((1 : Ω') ⊗ₜ[Ω] e)}

def AddBlockPullback.Statement : Prop :=
  ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] (ι κ : Type)
    [Fintype ι] [Fintype κ] (x : ι → Ω) (z : κ → Ω') (r : ℕ) (E : Type) [AddCommGroup E]
    [Module Ω E] (B : ChartBundle ℤ x r E),
    ∃ B' : ChartBundle ℤ (segreJoin (fun i => algebraMap Ω Ω' (x i)) z) r (Ω' ⊗[Ω] E),
      ∀ q, B'.lat q = pullLat x z B.lat q

instance joinFintype {K K' : Type} {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] : ∀ k, Fintype (Sum.elim ι ι' k)
  | Sum.inl k => inferInstanceAs (Fintype (ι k))
  | Sum.inr k => inferInstanceAs (Fintype (ι' k))

def joinPt {Ω' : Type} {K K' : Type} {ι : K → Type} {ι' : K' → Type} (y : (Σ k, ι k) → Ω')
    (z : (Σ k, ι' k) → Ω') : (Σ k : K ⊕ K', Sum.elim ι ι' k) → Ω'
  | ⟨Sum.inl k, i⟩ => y ⟨k, i⟩
  | ⟨Sum.inr k, i⟩ => z ⟨k, i⟩

def AddBlockNef.Statement : Prop :=
  ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] (K K' : Type)
    [Fintype K] [Fintype K'] (ι : K → Type) (ι' : K' → Type) [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] (y : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω') (a : K → ℤ),
    NefOnFibres (mCoordIdeal y) a →
    NefOnFibres (mCoordIdeal (joinPt (fun q => algebraMap Ω Ω' (y q)) z)) (Sum.elim a 0)

end Gluing

section Inhabitants

def Vandermonde₂ : Poly Unit 3 := delta Unit 3 * X ((), 0)

example : ReciprocityTheory.ChartRestriction.G.Geo.ChartBundle ℤ (fun _ : Fin 2 => (1 : ℚ)) 1 ℚ :=
  ReciprocityTheory.ChartRestriction.G.Geo.lineBundle ℤ _ 1

example : FiniteDimensional ℚ ℚ := inferInstance

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Antisym
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

section Rings

variable {Ω : Type} [Field Ω]





end Rings

section Join

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}



theorem addBlockPullback_of_chartBundlePullback (h : ChartBundlePullback.Statement) :
    IndefiniteRowSideFullHecke.Antisym.AddBlockPullback.Statement := by
  intro Ω Ω' _ _ _ _ ι κ _ _ x z r E _ _ B
  exact h Ω Ω' ι κ x z r E B

end Join

section AddBlock

variable {K : Type} {ι : K → Type} {κ : Type}

def addBlockToSum : Option K → K ⊕ Unit
  | none => Sum.inr ()
  | some k => Sum.inl k

def addBlockIdxToSigma :
    (Σ o, addBlockIdx ι κ o) → (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k)
  | ⟨none, i⟩ => ⟨Sum.inr (), i⟩
  | ⟨some k, i⟩ => ⟨Sum.inl k, i⟩

def sigmaToAddBlockIdx :
    (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k) → (Σ o, addBlockIdx ι κ o)
  | ⟨Sum.inr (), i⟩ => ⟨none, i⟩
  | ⟨Sum.inl k, i⟩ => ⟨some k, i⟩

def addBlockIdxEquiv :
    (Σ o, addBlockIdx ι κ o) ≃ (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => κ) k) where
  toFun := addBlockIdxToSigma
  invFun := sigmaToAddBlockIdx
  left_inv := by rintro ⟨_ | k, i⟩ <;> rfl
  right_inv := by rintro ⟨k | ⟨⟩, i⟩ <;> rfl




end AddBlock

section Readings

open IndefiniteRowSideFullHecke.Antisym

def ratsInReal : Subfield ℝ := (Rat.castHom ℝ).fieldRange

abbrev chartOne : Subalgebra ℤ ℝ := chartRing ℤ (fun _ : Unit => (1 : ℝ)) ()



abbrev zTwo : Subring ℝ := locAtIntPrime 2 chartOne.toSubring



def sqrtTwoLattice : Submodule zTwo ℝ := Submodule.span zTwo (Set.range ![(1 : ℝ), √2])






end Readings

end GroundTheory.Heights₂.Heights
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo TensorProduct

section Pullback

variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}

theorem algebraMap_mem_chartRing_joinPt (x : ι → Ω) (z : κ → Ω') (i : ι) (l : κ) (hz : z l ≠ 0)
    {a : Ω} (ha : a ∈ chartRing ℤ x i) :
    algebraMap Ω Ω' a ∈ chartRing ℤ (joinPt x z) (i, l) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have : algebraMap Ω Ω' (x j / x i) = joinPt x z (j, l) / joinPt x z (i, l) := by
      simp only [joinPt, segreJoin, map_div₀]
      rw [mul_div_mul_right _ _ hz]
    rw [this]
    exact div_mem_chartRing _ _ _
  | algebraMap n =>
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ n
  | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
  | mul y w _ _ hy hw => rw [map_mul]; exact mul_mem hy hw

theorem div_mem_chartRing_joinPt (x : ι → Ω) (z : κ → Ω') (j : ι) (l m : κ) (hx : x j ≠ 0) :
    z l / z m ∈ chartRing ℤ (joinPt x z) (j, m) := by
  have hx' : algebraMap Ω Ω' (x j) ≠ 0 := (map_ne_zero _).2 hx
  have : z l / z m = joinPt x z (j, l) / joinPt x z (j, m) := by
    simp only [joinPt, segreJoin]
    rw [mul_div_mul_left _ _ hx']
  rw [this]
  exact div_mem_chartRing _ _ _

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem one_tmul_smul (s : Ω) (v : E) :
    (1 : Ω') ⊗ₜ[Ω] (s • v) = algebraMap Ω Ω' s • ((1 : Ω') ⊗ₜ[Ω] v) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul,
    mul_one]

variable {r : ℕ}

theorem pullbackLat_stable {x : ι → Ω} (B : ChartBundle ℤ x r E) (z : κ → Ω') (q : ι × κ)
    {a : Ω'} (ha : a ∈ chartRing ℤ (joinPt x z) q) {e : Ω' ⊗[Ω] E} (he : e ∈ pullbackLat B z q) :
    a • e ∈ pullbackLat B z q := by
  induction he using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨a * b, mul_mem ha hb, v, hv, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add w w' _ _ hw hw' => rw [smul_add]; exact add_mem hw hw'
  | neg w _ hw => rw [smul_neg]; exact neg_mem hw

theorem smul_one_tmul_mem_pullbackLat {x : ι → Ω} (B : ChartBundle ℤ x r E) (z : κ → Ω')
    (q : ι × κ) {a : Ω'} (ha : a ∈ chartRing ℤ (joinPt x z) q) {v : E} (hv : v ∈ B.lat q.1) :
    a • ((1 : Ω') ⊗ₜ[Ω] v) ∈ pullbackLat B z q :=
  AddSubgroup.subset_closure ⟨a, ha, v, hv, rfl⟩

def pullbackBundle {x : ι → Ω} (B : ChartBundle ℤ x r E) (z : κ → Ω') :
    ChartBundle ℤ (joinPt x z) r (Ω' ⊗[Ω] E) where
  lat := pullbackLat B z
  stable q a ha e he := pullbackLat_stable B z q ha he
  frame q hq := by
    obtain ⟨i, l⟩ := q
    obtain ⟨hxi', hzl⟩ := mul_ne_zero_iff.1 hq
    have hxi : x i ≠ 0 := fun h => hxi' (by simp [h])
    obtain ⟨k, f, c, hf, hc, hsum, hfr⟩ := B.frame i hxi
    refine ⟨k, fun l' => algebraMap Ω Ω' (f l'), fun l' => algebraMap Ω Ω' (c l'),
      fun l' => algebraMap_mem_chartRing_joinPt x z i l hzl (hf l'),
      fun l' => algebraMap_mem_chartRing_joinPt x z i l hzl (hc l'), ?_, fun l' => ?_⟩
    · simp only [← map_mul, ← map_sum, hsum, map_one]
    obtain ⟨b, hli, hspan, hiff⟩ := hfr l'
    set R := chartRing ℤ (joinPt x z) (i, l)
    set F := algebraMap Ω Ω' (f l')
    have hF : F ∈ R := algebraMap_mem_chartRing_joinPt x z i l hzl (hf l')
    let bas : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hspan.ge
    let bb := Algebra.TensorProduct.basis Ω' bas
    have hbb : ∀ q, bb q = (1 : Ω') ⊗ₜ[Ω] b q := fun q => by
      rw [Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]
    have hrep : ∀ (a : Fin r → Ω') (q : Fin r), bb.repr (∑ q, a q • bb q) q = a q := fun a q => by
      rw [← bb.equivFun_symm_apply, ← bb.equivFun_apply, LinearEquiv.apply_symm_apply]

    have hRadd : ∀ a a' : Ω', (∃ n : ℕ, F ^ n * a ∈ R) → (∃ n : ℕ, F ^ n * a' ∈ R) →
        ∃ n : ℕ, F ^ n * (a + a') ∈ R := by
      rintro a a' ⟨n, hn⟩ ⟨n', hn'⟩
      refine ⟨n + n', ?_⟩
      have : F ^ (n + n') * (a + a') = F ^ n' * (F ^ n * a) + F ^ n * (F ^ n' * a') := by ring
      rw [this]
      exact add_mem (mul_mem (pow_mem hF _) hn) (mul_mem (pow_mem hF _) hn')
    refine ⟨fun q => (1 : Ω') ⊗ₜ[Ω] b q, ?_, ?_, fun e => ⟨?_, ?_⟩⟩
    · have := bb.linearIndependent
      simpa only [funext hbb] using this
    · have := bb.span_eq
      simpa only [funext hbb] using this
    · rintro ⟨n, hn⟩

      have key : ∀ w ∈ pullbackLat B z (i, l), ∀ q, ∃ m : ℕ, F ^ m * bb.repr w q ∈ R := by
        intro w hw
        induction hw using AddSubgroup.closure_induction with
        | mem w hw =>
          obtain ⟨a, ha, v, hv, rfl⟩ := hw
          obtain ⟨α, hα, hvα⟩ := (hiff v).1 ⟨0, by simpa using hv⟩
          have hv' : (1 : Ω') ⊗ₜ[Ω] v = ∑ q, algebraMap Ω Ω' (α q) • bb q := by
            rw [hvα, TensorProduct.tmul_sum]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [one_tmul_smul, hbb]
          intro q
          obtain ⟨m, hm⟩ := hα q
          refine ⟨m, ?_⟩
          rw [hv', map_smul, Finsupp.smul_apply, hrep, smul_eq_mul]
          have : F ^ m * (a * algebraMap Ω Ω' (α q)) = a * algebraMap Ω Ω' (f l' ^ m * α q) := by
            simp only [F, map_mul, map_pow]; ring
          rw [this]
          exact mul_mem ha (algebraMap_mem_chartRing_joinPt x z i l hzl hm)
        | zero => intro q; exact ⟨0, by simp⟩
        | add w w' _ _ hw hw' =>
          intro q
          rw [map_add, Finsupp.add_apply]
          exact hRadd _ _ (hw q) (hw' q)
        | neg w _ hw =>
          intro q
          obtain ⟨m, hm⟩ := hw q
          exact ⟨m, by rw [map_neg, Finsupp.neg_apply, mul_neg]; exact neg_mem hm⟩
      refine ⟨fun q => bb.repr e q, fun q => ?_, ?_⟩
      · obtain ⟨m, hm⟩ := key _ hn q
        refine ⟨m + n, ?_⟩
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add] at hm
        exact hm
      · conv_lhs => rw [← bb.sum_repr e]
        exact Finset.sum_congr rfl fun q _ => by rw [hbb]
    · rintro ⟨a, ha, rfl⟩

      have hbq : ∀ q, ∃ n : ℕ, F ^ n • ((1 : Ω') ⊗ₜ[Ω] b q) ∈ pullbackLat B z (i, l) := by
        intro q
        obtain ⟨n, hn⟩ := (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
          rcases eq_or_ne q' q with rfl | h
          · simp
          · simp [Pi.single_eq_of_ne h]⟩, by simp [Pi.single_apply]⟩
        refine ⟨n, ?_⟩
        have : F ^ n • ((1 : Ω') ⊗ₜ[Ω] b q) = (1 : Ω') • ((1 : Ω') ⊗ₜ[Ω] (f l' ^ n • b q)) := by
          rw [one_smul, one_tmul_smul, map_pow]
        rw [this]
        exact smul_one_tmul_mem_pullbackLat B z (i, l) (one_mem _) hn
      refine Finset.sum_induction _ (fun w => ∃ n : ℕ, F ^ n • w ∈ pullbackLat B z (i, l)) ?_
        ⟨0, by simp⟩ fun q _ => ?_
      · rintro w w' ⟨n, hn⟩ ⟨n', hn'⟩
        refine ⟨n + n', ?_⟩
        rw [show F ^ (n + n') • (w + w') = F ^ n' • (F ^ n • w) + F ^ n • (F ^ n' • w') by
          rw [smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n' n, smul_add]]
        exact add_mem (pullbackLat_stable B z _ (pow_mem hF _) hn)
          (pullbackLat_stable B z _ (pow_mem hF _) hn')
      · obtain ⟨n, hn⟩ := hbq q
        obtain ⟨m, hm⟩ := ha q
        refine ⟨m + n, ?_⟩
        rw [pow_add, mul_smul, smul_comm (F ^ n) (a q), ← mul_smul]
        exact pullbackLat_stable B z _ hm hn
  overlap q q' hq hq' e he := by
    obtain ⟨i, l⟩ := q
    obtain ⟨j, l₂⟩ := q'
    obtain ⟨hxi', -⟩ := mul_ne_zero_iff.1 hq
    obtain ⟨hxj', -⟩ := mul_ne_zero_iff.1 hq'
    have hxi : x i ≠ 0 := fun h => hxi' (by simp [h])
    have hxj : x j ≠ 0 := fun h => hxj' (by simp [h])
    have ht : joinPt x z (i, l) / joinPt x z (j, l₂) ∈ chartRing ℤ (joinPt x z) (j, l₂) :=
      div_mem_chartRing _ _ _
    induction he using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, v, hv, rfl⟩ := hw
      obtain ⟨m₁, hm₁⟩ := exists_pow_mul_mem_chartRing (o := ℤ) (joinPt x z) (i, l) (j, l₂) hq ha
      obtain ⟨m₂, hm₂⟩ := B.overlap i j hxi hxj v hv
      refine ⟨m₁ + m₂, ?_⟩
      have htt : joinPt x z (i, l) / joinPt x z (j, l₂) =
          algebraMap Ω Ω' (x i / x j) * (z l / z l₂) := by
        simp only [joinPt, segreJoin, map_div₀]
        rw [mul_div_mul_comm]
      have : (joinPt x z (i, l) / joinPt x z (j, l₂)) ^ (m₁ + m₂) • (a • ((1 : Ω') ⊗ₜ[Ω] v)) =
          ((joinPt x z (i, l) / joinPt x z (j, l₂)) ^ m₁ * a * (z l / z l₂) ^ m₂) •
            ((1 : Ω') ⊗ₜ[Ω] ((x i / x j) ^ m₂ • v)) := by
        rw [one_tmul_smul, smul_smul, smul_smul, map_pow]
        congr 1
        rw [htt]
        ring
      rw [this]
      exact smul_one_tmul_mem_pullbackLat B z (j, l₂)
        (mul_mem hm₁ (pow_mem (div_mem_chartRing_joinPt x z j l l₂ hxj) _)) hm₂
    | zero => exact ⟨0, by simp⟩
    | add w w' _ _ hw hw' =>
      obtain ⟨n, hn⟩ := hw
      obtain ⟨n', hn'⟩ := hw'
      refine ⟨n + n', ?_⟩
      rw [show (joinPt x z (i, l) / joinPt x z (j, l₂)) ^ (n + n') • (w + w') =
          (joinPt x z (i, l) / joinPt x z (j, l₂)) ^ n' •
              ((joinPt x z (i, l) / joinPt x z (j, l₂)) ^ n • w) +
            (joinPt x z (i, l) / joinPt x z (j, l₂)) ^ n •
              ((joinPt x z (i, l) / joinPt x z (j, l₂)) ^ n' • w') by
        rw [smul_smul, smul_smul, ← pow_add, ← pow_add, add_comm n' n, smul_add]]
      exact add_mem (pullbackLat_stable B z _ (pow_mem ht _) hn)
        (pullbackLat_stable B z _ (pow_mem ht _) hn')
    | neg w _ hw =>
      obtain ⟨n, hn⟩ := hw
      exact ⟨n, by rw [smul_neg]; exact neg_mem hn⟩

theorem chartBundlePullback_holds : ChartBundlePullback.Statement :=
  fun _ _ _ _ _ _ _ _ _ _ z _ _ _ _ B => ⟨pullbackBundle B z, fun _ => rfl⟩

end Pullback

theorem AddBlockPullback.equiv :
    ChartBundlePullback.Statement ↔ IndefiniteRowSideFullHecke.Antisym.AddBlockPullback.Statement :=
  ⟨addBlockPullback_of_chartBundlePullback, fun _ => chartBundlePullback_holds⟩

end GroundTheory.Heights₂.Heights
end
end
