import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorEllPBound
import Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantProjectionExtremalFormula
import Lemmata.GeneralBFactLeftAltForm.MQ

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section defs
variable {n : ℕ} {K : Type} [Field K] {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

def IsSubrepresentation (E : GLOps n K V) (W : Submodule K V) : Prop := ∀ a b, ∀ x ∈ W, E a b x ∈ W

def IsEquivariantMap (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') : Prop := ∀ a b x, T (E a b x) = E' a b (T x)

def restrictRepresentation (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) : GLOps n K W :=
  fun a b => (E a b).restrict (h a b)

def homRepresentation (E : GLOps n K V) (E' : GLOps n K V') : GLOps n K (V →ₗ[K] V') :=
  fun a b => LinearMap.llcomp K V V' V' (E' a b) - LinearMap.lcomp K V' (E a b)

def cyclicSubmodule (E : GLOps n K V) (v : V) : Submodule K V := Submodule.span K {x | ∃ u ∈ Umon E, x = u v}

end defs

def RestrictionIsRepresentation : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∀ (W : Submodule K V) (h : IsSubrepresentation E W), IsGLRep (restrictRepresentation E W h)

def HomSpaceIsRepresentation : Prop :=
  ∀ (n : ℕ) (K V V' : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (E : GLOps n K V) (E' : GLOps n K V'),
    IsGLRep E → IsGLRep E' → IsGLRep (homRepresentation E E')

def IsotypicSubmodulesSpanTop : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → (⨆ mu, isoSub E mu) = ⊤

def InvariantProjectionExists : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∃ P : Module.End K V, IsInvProj E P

def EquivariantCommutesInvariantProjection : Prop :=
  ∀ (n : ℕ) (K V V' : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (E : GLOps n K V) (E' : GLOps n K V'),
    IsGLRep E → IsGLRep E' → ∀ T : V →ₗ[K] V', IsEquivariantMap E E' T →
    ∀ (P : Module.End K V) (P' : Module.End K V'), IsInvProj E P → IsInvProj E' P' → ∀ x, T (P x) = P' (T x)

def OperatorsKillInvariantProjection : Prop :=
  ∀ (n : ℕ) (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V), IsGLRep E → ∀ P : Module.End K V, IsInvProj E P → ∀ x a b, E a b (P x) = 0

def IsotypicProjectorTraceFormula : Prop :=
  ∀ (n : ℕ) (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (E : GLOps n K W), IsGLRep E → ∀ (lam : Fin n → ℤ) (e : Module.End K W), IsIsoProj E lam e →
    ∀ v0, IsHWV E lam v0 → ∀ (hL : IsSubrepresentation E (cyclicSubmodule E v0))
      (P : Module.End K (cyclicSubmodule E v0 →ₗ[K] W)), IsInvProj (homRepresentation (restrictRepresentation E _ hL) E) P →
      ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι K (cyclicSubmodule E v0)) (m : W),
        (Fintype.card ι : K) • ∑ i, P ((b.coord i).smulRight m) (b i) = e m

section lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

def homLattice (M : Submodule O W) (L : Submodule (KK O) W) : Submodule O (L →ₗ[KK O] W) where
  carrier := {f | ∀ x : L, (x : W) ∈ M → f x ∈ M}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun hf hg x hx => by simpa using M.add_mem (hf x hx) (hg x hx)
  smul_mem' := fun c f hf x hx => by simpa using M.smul_mem c (hf x hx)

end lat

def LatticeAdaptedBasisExists : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (W : Type) [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (M : Submodule O W), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ L : Submodule (KK O) W, ∃ (d : ℕ) (b : Module.Basis (Fin d) (KK O) L), (∀ i, ((b i : L) : W) ∈ M) ∧
      ∀ x : L, (x : W) ∈ M → ∀ i, ∃ o : O, b.coord i x = algebraMap O (KK O) o

def HomLatticeDividedPowerStable : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)]
    (n : ℕ) (W : Type) [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]
    [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W), IsGLRep E →
    ∀ M : Submodule O W, UZLattice E M → MQ (K := KK O) M = ⊤ →
    ∀ (L : Submodule (KK O) W) (hL : IsSubrepresentation E L),
      UZLattice (homRepresentation (restrictRepresentation E L hL) E) (homLattice M L) ∧ MQ (K := KK O) (homLattice M L) = ⊤

def HomRepEllBoundedByTarget : Prop :=
  ∀ (n : ℕ) (K W : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (E : GLOps n K W), IsGLRep E → ∀ (L : Submodule K W) (hL : IsSubrepresentation E L),
      ellP (homRepresentation (restrictRepresentation E L hL) E) ⊤ ≤ ellOf E ⊤

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem charZero_fraction_field_of_setting {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  have hO : CharZero O := by
    rcases S with ⟨w, hw, hpm, hp0, -⟩
    rcases CharP.char_is_prime_or_zero O (ringChar O) with hq | hq
    · exfalso
      have hne : p ≠ ringChar O := by
        rintro h
        apply hp0
        rw [h]
        exact CharP.cast_eq_zero O (ringChar O)
      have hcop : Nat.gcd p (ringChar O) = 1 := (Nat.coprime_primes hp hq).mpr hne
      have key : (1 : O) = (p : O) * (Nat.gcdA p (ringChar O) : O) := by
        have h := congrArg (fun z : ℤ => (z : O)) (Nat.gcd_eq_gcd_ab p (ringChar O))
        simp only [hcop, Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
          CharP.cast_eq_zero, zero_mul, add_zero] at h
        exact h
      have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := key ▸ Ideal.mul_mem_right _ _ hpm
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · haveI : CharP O 0 := hq ▸ ringChar.charP O
      exact CharP.charP_to_charZero O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))

theorem cyclicSubmodule_isSubrepresentation {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (v : V) :
    IsSubrepresentation E (cyclicSubmodule E v) := by
  unfold IsSubrepresentation cyclicSubmodule
  intro a b x hx
  have hle : Submodule.span K {x | ∃ u ∈ Umon E, x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    refine ⟨E a b * u, ?_, rfl⟩
    unfold Umon at hu ⊢
    exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu
  exact hle hx

theorem log_bound_monotone (p n : ℕ) {k l : ℕ} (h : k ≤ l) : deF p n k ≤ deF p n l := by
  unfold deF
  exact Nat.log_mono_right (by omega)

theorem pow_smul_mem_of_le' {O W : Type} [CommRing O] [AddCommGroup W] [Module O W] (M : Submodule O W) (c : O) {a b : ℕ}
    (hab : a ≤ b) {z : W} (h : c ^ a • z ∈ M) : c ^ b • z ∈ M := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_comm, mul_smul]
  exact M.smul_mem _ h



end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section wt
variable {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSp_iff_diagonal_apply (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem linearMap_ext_on_weightSpaces {V' : Type} [AddCommGroup V'] [Module K V'] (E : GLOps n K V) (hE : IsGLRep E)
    (f g : V →ₗ[K] V') (h : ∀ mu, ∀ x ∈ weightSp E mu, f x = g x) : f = g := by
  have hle : (⨆ mu, weightSp E mu) ≤ LinearMap.eqLocus f g := iSup_le fun mu x hx => h mu x hx
  ext x
  have : x ∈ (⨆ mu, weightSp E mu) := by rw [hE.2.2]; trivial
  exact hle this

open Classical in

def lagrangeWeightFactor (E : GLOps n K V) (mu nu : Fin n → ℤ) : Module.End K V :=
  if h : ∃ a, nu a ≠ mu a then
    (((mu h.choose : K) - (nu h.choose : K))⁻¹) • (E h.choose h.choose - (nu h.choose : K) • (1 : Module.End K V))
  else 1

def lagrangeOperator (E : GLOps n K V) (mu : Fin n → ℤ) : List (Fin n → ℤ) → Module.End K V
  | [] => 1
  | nu :: l => lagrangeWeightFactor E mu nu * lagrangeOperator E mu l

theorem lagrangeFactor_acts_by_scalar (E : GLOps n K V) (mu nu ka : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ka) :
    ∃ c : K, lagrangeWeightFactor E mu nu x = c • x := by
  unfold lagrangeWeightFactor
  split_ifs with h
  · refine ⟨((mu h.choose : K) - (nu h.choose : K))⁻¹ * ((ka h.choose : K) - (nu h.choose : K)), ?_⟩
    simp [(mem_weightSp_iff_diagonal_apply E ka x).1 hx, sub_smul, mul_smul, smul_sub]
  · exact ⟨1, by simp⟩

theorem lagrangeFactor_fixes_own_weight [CharZero K] (E : GLOps n K V) (mu nu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    lagrangeWeightFactor E mu nu x = x := by
  unfold lagrangeWeightFactor
  split_ifs with h
  · have hne : ((mu h.choose : K) - (nu h.choose : K)) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast (h.choose_spec).symm
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, (mem_weightSp_iff_diagonal_apply E mu x).1 hx, Module.End.one_apply]
    rw [← sub_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · simp

theorem lagrangeFactor_kills_other_weight (E : GLOps n K V) (mu nu : Fin n → ℤ) (hne : nu ≠ mu) (x : V) (hx : x ∈ weightSp E nu) :
    lagrangeWeightFactor E mu nu x = 0 := by
  have h : ∃ a, nu a ≠ mu a := by
    by_contra hc; exact hne (funext fun a => by_contra fun h => hc ⟨a, h⟩)
  unfold lagrangeWeightFactor
  rw [dif_pos h]
  simp [(mem_weightSp_iff_diagonal_apply E nu x).1 hx]

theorem lagrangeFactor_preserves_stable (E : GLOps n K V) (mu nu : Fin n → ℤ) (W : Submodule K V)
    (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W) (x : V) (hx : x ∈ W) : lagrangeWeightFactor E mu nu x ∈ W := by
  unfold lagrangeWeightFactor
  split_ifs with h
  · simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply]
    exact W.smul_mem _ (W.sub_mem (hW _ x hx) (W.smul_mem _ hx))
  · simpa using hx

theorem lagrangeOperator_acts_by_scalar (E : GLOps n K V) (mu ka : Fin n → ℤ) (l : List (Fin n → ℤ)) (x : V)
    (hx : x ∈ weightSp E ka) : ∃ c : K, lagrangeOperator E mu l x = c • x := by
  induction l with
  | nil => exact ⟨1, by simp [lagrangeOperator]⟩
  | cons nu l ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨c', hc'⟩ := lagrangeFactor_acts_by_scalar E mu nu ka x hx
    exact ⟨c * c', by simp [lagrangeOperator, hc, hc', smul_smul]⟩

theorem lagrangeOperator_fixes_own_weight [CharZero K] (E : GLOps n K V) (mu : Fin n → ℤ) (l : List (Fin n → ℤ)) (x : V)
    (hx : x ∈ weightSp E mu) : lagrangeOperator E mu l x = x := by
  induction l with
  | nil => simp [lagrangeOperator]
  | cons nu l ih => simp [lagrangeOperator, ih, lagrangeFactor_fixes_own_weight E mu nu x hx]

theorem lagrangeOperator_kills_listed (E : GLOps n K V) (mu ka : Fin n → ℤ) (hne : ka ≠ mu) (l : List (Fin n → ℤ))
    (hl : ka ∈ l) (x : V) (hx : x ∈ weightSp E ka) : lagrangeOperator E mu l x = 0 := by
  induction l with
  | nil => simp at hl
  | cons nu l ih =>
    obtain ⟨c, hc⟩ := lagrangeOperator_acts_by_scalar E mu ka l x hx
    rcases List.mem_cons.1 hl with h | h
    · subst h
      simp [lagrangeOperator, hc, lagrangeFactor_kills_other_weight E mu ka hne x hx]
    · simp [lagrangeOperator, ih h]

theorem lagrangeOperator_preserves_stable (E : GLOps n K V) (mu : Fin n → ℤ) (l : List (Fin n → ℤ)) (W : Submodule K V)
    (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W) (x : V) (hx : x ∈ W) : lagrangeOperator E mu l x ∈ W := by
  induction l with
  | nil => simpa [lagrangeOperator] using hx
  | cons nu l ih => simpa [lagrangeOperator] using lagrangeFactor_preserves_stable E mu nu W hW _ ih

theorem finitely_many_weights_span [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) :
    ∃ s : Finset (Fin n → ℤ), (⨆ mu ∈ s, weightSp E mu) = ⊤ := by
  have hc : IsCompactElement (⊤ : Submodule K V) :=
    (Submodule.fg_iff_compact _).1 (Module.finite_def.1 inferInstance)
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hc (weightSp E) (by rw [hE.2.2])
  exact ⟨s, top_le_iff.1 hs⟩

theorem weightSpace_eq_bot_outside_support [CharZero K] (E : GLOps n K V) (s : Finset (Fin n → ℤ))
    (hs : (⨆ mu ∈ s, weightSp E mu) = ⊤) (ka : Fin n → ℤ) (hk : ka ∉ s) : weightSp E ka = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : lagrangeOperator E ka s.toList x = x := lagrangeOperator_fixes_own_weight E ka _ x hx
  have hle : (⨆ mu ∈ s, weightSp E mu) ≤ LinearMap.ker (lagrangeOperator E ka s.toList) := by
    refine iSup₂_le fun mu hmu y hy => ?_
    exact lagrangeOperator_kills_listed E ka mu (fun h => hk (h ▸ hmu)) _ (Finset.mem_toList.2 hmu) y hy
  have h2 : x ∈ (⨆ mu ∈ s, weightSp E mu) := by rw [hs]; trivial
  have h3 := hle h2
  rw [LinearMap.mem_ker, h1] at h3
  simpa using h3

theorem weight_projections_exist [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) :
    ∃ (s : Finset (Fin n → ℤ)) (π : (Fin n → ℤ) → Module.End K V),
      (∀ mu, IsWtProj E mu (π mu)) ∧
      (∀ mu, ∀ W : Submodule K V, (∀ a, ∀ x ∈ W, E a a x ∈ W) → ∀ x ∈ W, π mu x ∈ W) ∧
      (∀ mu, mu ∉ s → weightSp E mu = ⊥) ∧
      (∀ mu x, π mu x ∈ weightSp E mu) ∧
      (∀ x, ∑ mu ∈ s, π mu x = x) := by
  classical
  obtain ⟨s, hs⟩ := finitely_many_weights_span E hE
  have hbot := weightSpace_eq_bot_outside_support E s hs
  have hπ : ∀ mu, IsWtProj E mu (lagrangeOperator E mu s.toList) := by
    intro mu
    refine ⟨fun x hx => lagrangeOperator_fixes_own_weight E mu _ x hx, fun nu hnu x hx => ?_⟩
    by_cases hm : nu ∈ s
    · exact lagrangeOperator_kills_listed E mu nu hnu _ (Finset.mem_toList.2 hm) x hx
    · rw [hbot nu hm] at hx
      rw [(Submodule.mem_bot K).1 hx, map_zero]
  refine ⟨s, fun mu => lagrangeOperator E mu s.toList, hπ, fun mu W hW x hx => lagrangeOperator_preserves_stable E mu _ W hW x hx, hbot, ?_, ?_⟩
  · intro mu x
    have : LinearMap.range (lagrangeOperator E mu s.toList) ≤ weightSp E mu := by
      rw [LinearMap.range_eq_map, ← hE.2.2, Submodule.map_iSup]
      refine iSup_le fun nu => ?_
      rintro _ ⟨y, hy, rfl⟩
      by_cases h : nu = mu
      · subst h; rw [(hπ nu).1 y hy]; exact hy
      · rw [(hπ mu).2 nu h y hy]; exact Submodule.zero_mem _
    exact this ⟨x, rfl⟩
  · intro x
    have : (∑ mu ∈ s, lagrangeOperator E mu s.toList) = (1 : Module.End K V) := by
      refine linearMap_ext_on_weightSpaces E hE _ _ fun nu y hy => ?_
      rw [LinearMap.sum_apply, Module.End.one_apply]
      by_cases hm : nu ∈ s
      · rw [Finset.sum_eq_single nu (fun mu _ hmu => (hπ mu).2 nu (Ne.symm hmu) y hy) (fun h => absurd hm h)]
        exact (hπ nu).1 y hy
      · rw [hbot nu hm] at hy
        rw [(Submodule.mem_bot K).1 hy]; simp
    have h2 := congrArg (fun f : Module.End K V => f x) this
    simpa [LinearMap.sum_apply] using h2

end wt

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

@[simp] theorem restrictRepresentation_coe (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) (a b : Fin n) (x : W) :
    ((restrictRepresentation E W h a b x : W) : V) = E a b x := rfl

@[simp] theorem homRepresentation_apply (E : GLOps n K V) (E' : GLOps n K V') (a b : Fin n) (f : V →ₗ[K] V') (x : V) :
    homRepresentation E E' a b f x = E' a b (f x) - f (E a b x) := by
  simp [homRepresentation]

theorem restrict_mem_weightSpace_iff (E : GLOps n K V) (W : Submodule K V) (h : IsSubrepresentation E W) (mu : Fin n → ℤ) (x : W) :
    x ∈ weightSp (restrictRepresentation E W h) mu ↔ (x : V) ∈ weightSp E mu := by
  rw [mem_weightSp_iff_diagonal_apply, mem_weightSp_iff_diagonal_apply]
  constructor
  · intro hx a
    have e := congrArg Subtype.val (hx a)
    simpa using e
  · intro hx a
    ext
    simpa using hx a

theorem restrictRepresentation_isRep [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V)
    (h : IsSubrepresentation E W) : IsGLRep (restrictRepresentation E W h) := by
  refine ⟨fun a b c d => ?_, fun x => ⟨⊤, inferInstance, Submodule.mem_top,
    fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  · refine LinearMap.ext fun x => Subtype.ext ?_
    have e := congrArg (fun f => f (x : V)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, restrictRepresentation_coe]
    rw [e]
    split_ifs <;> simp
  · obtain ⟨s, π, -, hinv, -, hmem, hsum⟩ := weight_projections_exist E hE
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ mu ∈ s, (⟨π mu x, hinv mu W (fun a y hy => h a a y hy) x x.2⟩ : W) := by
      ext
      simp [hsum]
    rw [hx]
    refine Submodule.sum_mem _ fun mu _ => ?_
    refine Submodule.mem_iSup_of_mem mu ?_
    rw [restrict_mem_weightSpace_iff]
    exact hmem mu x

theorem weightProjection_diagonal_apply_eq_smul [CharZero K] (E : GLOps n K V) (hE : IsGLRep E) (nu : Fin n → ℤ) (π : Module.End K V)
    (hπ : IsWtProj E nu π) (a : Fin n) (x : V) : π (E a a x) = (nu a : K) • π x := by
  have hx : x ∈ (⨆ mu, weightSp E mu) := hE.2.2 ▸ Submodule.mem_top
  refine Submodule.iSup_induction (p := weightSp E) (motive := fun y => π (E a a y) = (nu a : K) • π y) hx
    (fun mu y hy => ?_) ?_ (fun y w hy hw => ?_)
  · rw [(mem_weightSp_iff_diagonal_apply E mu y).1 hy a, map_smul]
    by_cases hmu : mu = nu
    · subst hmu
      rfl
    · rw [hπ.2 mu hmu y hy, smul_zero, smul_zero]
  · simp
  · simp only [map_add, hy, hw, smul_add]

theorem homRepresentation_isRep [CharZero K] [FiniteDimensional K V] [FiniteDimensional K V'] (E : GLOps n K V)
    (E' : GLOps n K V') (hE : IsGLRep E) (hE' : IsGLRep E') : IsGLRep (homRepresentation E E') := by
  refine ⟨fun a b c d => ?_, fun f => ⟨⊤, inferInstance, Submodule.mem_top,
    fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  · ext f x
    have h1 := congrArg (fun g => g (f x)) (hE'.1 a b c d)
    have h2 := congrArg (fun g => f (g x)) (hE.1 a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub] at h1 h2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, homRepresentation_apply, map_sub]
    split_ifs at h1 h2 ⊢ <;>
      simp only [LinearMap.zero_apply, map_zero, sub_zero, zero_sub, homRepresentation_apply, map_sub,
        map_neg] at h1 h2 ⊢ <;>
      (rw [eq_add_of_sub_eq h1, eq_add_of_sub_eq h2]; abel)
  · obtain ⟨s, π, hπ, -, -, -, hsum⟩ := weight_projections_exist E hE
    obtain ⟨s', π', -, -, -, hmem', hsum'⟩ := weight_projections_exist E' hE'
    rw [eq_top_iff]
    intro f _
    have hf : f = ∑ mu ∈ s, ∑ mu' ∈ s', (π' mu').comp (f.comp (π mu)) := by
      ext x
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      rw [Finset.sum_comm]
      simp only [← map_sum]
      rw [hsum x, hsum' (f x)]
    rw [hf]
    refine Submodule.sum_mem _ fun mu _ => Submodule.sum_mem _ fun mu' _ => ?_
    refine Submodule.mem_iSup_of_mem (mu' - mu) ?_
    rw [mem_weightSp_iff_diagonal_apply]
    intro a
    ext x
    simp only [homRepresentation_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [weightProjection_diagonal_apply_eq_smul E hE mu (π mu) (hπ mu) a x, map_smul, map_smul,
      (mem_weightSp_iff_diagonal_apply E' mu' _).1 (hmem' mu' _) a]
    simp only [Pi.sub_apply, Int.cast_sub, sub_smul]

theorem root_differences_bddAbove [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (W : Submodule K V) :
    BddAbove {k : ℕ | ∃ mu ∈ wtsOf E W, ∃ nu ∈ wtsOf E W, ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} := by
  obtain ⟨s, hs⟩ := finitely_many_weights_span E hE
  refine ⟨s.sup fun mu => s.sup fun nu => Finset.univ.sup fun a => (mu a - nu a).toNat, ?_⟩
  rintro k ⟨mu, hmu, nu, hnu, a, b, hab, heq⟩
  have hmu' : mu ∈ s := by
    by_contra hc
    apply hmu
    rw [weightSpace_eq_bot_outside_support E s hs mu hc, bot_inf_eq]
  have hnu' : nu ∈ s := by
    by_contra hc
    apply hnu
    rw [weightSpace_eq_bot_outside_support E s hs nu hc, bot_inf_eq]
  have hk : mu a - nu a = (k : ℤ) := by
    have e := congrFun heq a
    simp only [Pi.sub_apply, Pi.smul_apply, rootW, Pi.single_eq_same, Pi.single_eq_of_ne hab,
      sub_zero, smul_eq_mul, mul_one] at e
    exact e
  have hk' : k ≤ (mu a - nu a).toNat := by omega
  exact Finset.le_sup_of_le hmu' (Finset.le_sup_of_le hnu' (Finset.le_sup_of_le (Finset.mem_univ a) hk'))

end

theorem restriction_is_representation : RestrictionIsRepresentation := by
  intro n K V _ _ _ _ _ E hE W h
  exact restrictRepresentation_isRep E hE W h

theorem hom_space_is_representation : HomSpaceIsRepresentation := by
  intro n K V V' _ _ _ _ _ _ _ _ E E' hE hE'
  exact homRepresentation_isRep E E' hE hE'


end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

theorem exists_clear_denominators_alt (M : Submodule O W) (y : W) (hy : y ∈ MQ (K := KK O) M) : ∃ a : O, a ≠ 0 ∧ a • y ∈ M := by
  first | exact Bl.general_b_fact_left_alt_form.goal1 .. | (apply Bl.general_b_fact_left_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_alt_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_alt_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_alt_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_alt_form.goal1 <;> first | assumption | infer_instance)

def latticeInter (M : Submodule O W) (L : Submodule (KK O) W) : Submodule O L :=
  M.comap (L.subtype.restrictScalars O)


theorem latticeInter_isLattice (M : Submodule O W) (hfg : M.FG) (hMQ : MQ (K := KK O) M = ⊤) (L : Submodule (KK O) W) :
    Submodule.IsLattice (KK O) (latticeInter M L) where
  fg := by
    have hN : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hfg
    refine Submodule.fg_of_fg_map_injective (L.subtype.restrictScalars O) (fun x y h => Subtype.ext h) ?_
    refine (isNoetherian_submodule.1 hN) _ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  span_eq_top := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_clear_denominators_alt M (x : W) (by rw [hMQ]; trivial)
    have ha1 : algebraMap O (KK O) a ≠ 0 := by
      simpa using (IsFractionRing.injective O (KK O)).ne ha
    have h1 : a • x ∈ latticeInter M L := hax
    have h2 : x = (algebraMap O (KK O) a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul (KK O) a x, smul_smul, inv_mul_cancel₀ ha1, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end lat

theorem lattice_adapted_basis_exists : LatticeAdaptedBasisExists := by
  intro O _ _ _ W _ _ _ _ _ M hfg hMQ L
  haveI := latticeInter_isLattice M hfg hMQ L
  haveI : Module.Finite O (latticeInter M L) := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (A := KK O))
  let bO := Module.finBasis O (latticeInter M L)
  refine ⟨_, bO.extendOfIsLattice (KK O), fun i => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.extendOfIsLattice_apply]
    exact (bO i).2
  · obtain ⟨c, hc⟩ : ∃ c : Fin _ → O, x = ∑ j, (algebraMap O (KK O) (c j)) • (bO.extendOfIsLattice (KK O)) j := by
      refine ⟨fun j => bO.repr ⟨x, hx⟩ j, ?_⟩
      have h2 := congrArg (fun z : latticeInter M L => (z : L)) (bO.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h2
      refine h2.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [Module.Basis.extendOfIsLattice_apply, algebraMap_smul]
    refine ⟨c i, ?_⟩
    rw [hc, map_sum]
    simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section pw
variable {n : ℕ} {K : Type} [Field K] {L W : Type} [AddCommGroup L] [Module K L] [AddCommGroup W] [Module K W]

theorem llcomp_pow_apply (X : Module.End K W) (m : ℕ) (f : L →ₗ[K] W) :
    ((LinearMap.llcomp K L W W X) ^ m) f = (X ^ m) ∘ₗ f := by
  induction m generalizing f with
  | zero =>
    ext x
    simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc]
    rfl

theorem lcomp_pow_apply (Y : Module.End K L) (j : ℕ) (f : L →ₗ[K] W) :
    ((LinearMap.lcomp K W Y) ^ j) f = f ∘ₗ (Y ^ j) := by
  induction j generalizing f with
  | zero =>
    ext x
    simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ', Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    rfl

theorem homRepresentation_pow_apply (EL : GLOps n K L) (E : GLOps n K W) (a b : Fin n) (k : ℕ) (f : L →ₗ[K] W) (x : L) :
    ((homRepresentation EL E a b) ^ k) f x =
      ∑ m ∈ range (k + 1), ((k.choose m : K) * (-1) ^ (k - m)) • (E a b ^ m) (f ((EL a b ^ (k - m)) x)) := by
  have hc : Commute (LinearMap.llcomp K L W W (E a b)) ((-1 : K) • LinearMap.lcomp K W (EL a b)) := by
    refine Commute.smul_right ?_ (-1 : K)
    ext g y
    rfl
  have ht : homRepresentation EL E a b =
      LinearMap.llcomp K L W W (E a b) + (-1 : K) • LinearMap.lcomp K W (EL a b) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    rfl
  rw [ht, hc.add_pow, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Module.End.mul_apply, Module.End.natCast_apply, smul_pow, LinearMap.smul_apply,
    map_nsmul, map_smul, llcomp_pow_apply, lcomp_pow_apply, LinearMap.comp_apply]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul]

end pw

section lat
variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

theorem restrictRepresentation_pow_coe (E : GLOps n (KK O) W) (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a b : Fin n) (j : ℕ)
    (x : L) : (((restrictRepresentation E L hL a b) ^ j) x : W) = (E a b ^ j) (x : W) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

theorem int_smul_mem_lattice (M : Submodule O W) (z : ℤ) {x : W} (hx : x ∈ M) : ((z : ℤ) : KK O) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem weightProjection_preserves_lattice [CharZero (KK O)] [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W) (hE : IsGLRep E)
    (M : Submodule O W) (hM : UZStable (O := O) E M) (mu : Fin n → ℤ) (π : Module.End (KK O) W)
    (hπ : IsWtProj E mu π) : ∀ x ∈ M, π x ∈ M := by
  classical
  obtain ⟨sh, shwt, shM⟩ : ∃ sh : Fin n → ℤ → ℕ → Module.End (KK O) W,
      (∀ a c d ρ x, x ∈ weightSp E ρ → sh a c d x = ((Ring.choose (ρ a + c) d : ℤ) : KK O) • x) ∧
      (∀ a c d x, x ∈ M → sh a c d x ∈ M) := by
    refine ⟨fun a c d => ∑ ij ∈ antidiagonal d, ((Ring.choose c ij.2 : ℤ) : KK O) • binomE E a ij.1,
      ?_, ?_⟩
    · intro a c d ρ x hx
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, binomial_diagonal_apply_weight E a ρ x hx, smul_smul]
      rw [← Finset.sum_smul, Ring.add_choose_eq d (Commute.all _ _)]
      push_cast
      congr 1
      exact Finset.sum_congr rfl fun ij _ => by ring
    · intro a c d x hx
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun ij _ => ?_
      rw [LinearMap.smul_apply]
      exact int_smul_mem_lattice M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)
  have hT : ∀ nu : Fin n → ℤ, ∃ (T : Module.End (KK O) W) (h : (Fin n → ℤ) → ℤ), h mu = 1 ∧
      (nu ≠ mu → h nu = 0) ∧ (∀ ρ, ∀ x ∈ weightSp E ρ, T x = ((h ρ : ℤ) : KK O) • x) ∧
      ∀ x ∈ M, T x ∈ M := by
    intro nu
    by_cases hne : nu = mu
    · refine ⟨1, fun _ => 1, rfl, fun h => absurd hne h, fun ρ x _ => by simp, fun x hx => by simpa using hx⟩
    · obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
      rcases lt_or_gt_of_ne ha with hlt | hgt
      · obtain ⟨d, hd⟩ : ∃ d : ℕ, mu a - nu a = (d : ℤ) := ⟨(mu a - nu a).toNat, by omega⟩
        have hd0 : 0 < d := by omega
        refine ⟨sh a (-(nu a)) d, fun ρ => Ring.choose (ρ a + -(nu a)) d, ?_, ?_, ?_, ?_⟩
        · show Ring.choose (mu a + -(nu a)) d = 1
          rw [show mu a + -(nu a) = ((d : ℕ) : ℤ) by omega, Ring.choose_natCast, Nat.choose_self]
          rfl
        · intro _
          show Ring.choose (nu a + -(nu a)) d = 0
          rw [show nu a + -(nu a) = ((0 : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_eq_zero_of_lt hd0]
          rfl
        · intro ρ x hx
          exact shwt a _ _ ρ x hx
        · intro x hx
          exact shM a _ _ x hx
      · obtain ⟨d, hd⟩ : ∃ d : ℕ, nu a - mu a = (d : ℤ) := ⟨(nu a - mu a).toNat, by omega⟩
        refine ⟨sh a (-(mu a)) 0 - sh a (-(mu a)) d,
          fun ρ => Ring.choose (ρ a + -(mu a)) 0 - Ring.choose (ρ a + -(mu a)) d, ?_, ?_, ?_, ?_⟩
        · show Ring.choose (mu a + -(mu a)) 0 - Ring.choose (mu a + -(mu a)) d = 1
          have hd0 : 0 < d := by omega
          rw [Ring.choose_zero_right, show mu a + -(mu a) = ((0 : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_eq_zero_of_lt hd0]
          rfl
        · intro _
          show Ring.choose (nu a + -(mu a)) 0 - Ring.choose (nu a + -(mu a)) d = 0
          rw [Ring.choose_zero_right, show nu a + -(mu a) = ((d : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_self]
          rfl
        · intro ρ x hx
          rw [LinearMap.sub_apply, shwt a _ _ ρ x hx, shwt a _ _ ρ x hx, ← sub_smul]
          push_cast
          rfl
        · intro x hx
          rw [LinearMap.sub_apply]
          exact M.sub_mem (shM a _ _ x hx) (shM a _ _ x hx)
  have hproj : ∀ F : Finset (Fin n → ℤ), ∃ (P : Module.End (KK O) W) (g : (Fin n → ℤ) → ℤ), g mu = 1 ∧
      (∀ nu ∈ F, nu ≠ mu → g nu = 0) ∧ (∀ nu, ∀ x ∈ weightSp E nu, P x = ((g nu : ℤ) : KK O) • x) ∧
      ∀ x ∈ M, P x ∈ M := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      exact ⟨1, fun _ => 1, rfl, by simp, fun nu x _ => by simp, fun x hx => by simpa using hx⟩
    | insert nu F hnu ih =>
      obtain ⟨P, g, hg1, hg0, hgw, hgM⟩ := ih
      obtain ⟨T, h, hh1, hh0, hhw, hhM⟩ := hT nu
      refine ⟨T * P, fun ρ => h ρ * g ρ, by simp [hh1, hg1], ?_, ?_, ?_⟩
      · intro ν hν hne
        rcases Finset.mem_insert.1 hν with rfl | hν'
        · simp [hh0 hne]
        · simp [hg0 ν hν' hne]
      · intro ρ x hx
        rw [Module.End.mul_apply, hgw ρ x hx, map_smul, hhw ρ x hx, smul_smul]
        congr 1
        push_cast
        ring
      · intro x hx
        exact hhM _ (hgM x hx)
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin n → ℤ), (⊤ : Submodule (KK O) W) ≤ ⨆ nu ∈ F, weightSp E nu := by
    let bs := Module.finBasis (KK O) W
    have hb : ∀ i, ∃ s : Finset (Fin n → ℤ), bs i ∈ ⨆ nu ∈ s, weightSp E nu := by
      intro i
      apply Submodule.mem_iSup_iff_exists_finset.1
      rw [hE.2.2]
      exact Submodule.mem_top
    choose s hs using hb
    refine ⟨Finset.univ.biUnion s, ?_⟩
    rw [← bs.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hmono : (⨆ nu ∈ s i, weightSp E nu) ≤ ⨆ nu ∈ Finset.univ.biUnion s, weightSp E nu :=
      biSup_mono fun nu hnu => Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hnu⟩
    exact hmono (hs i)
  obtain ⟨P, g, hg1, hg0, hgw, hgM⟩ := hproj F
  have hπP : π = P := by
    have hle : (⨆ nu ∈ F, weightSp E nu) ≤ LinearMap.ker (π - P) := by
      refine iSup₂_le fun nu hnu => ?_
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hgw nu x hx]
      by_cases h : nu = mu
      · subst h
        rw [hπ.1 x hx, hg1]
        simp
      · rw [hπ.2 nu h x hx, hg0 nu hnu h]
        simp
    ext x
    have hx := hle (hF (Submodule.mem_top (x := x)))
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
    exact hx
  intro x hx
  rw [hπP]
  exact hgM x hx

theorem homLattice_dividedPower_stable [CharZero (KK O)] (E : GLOps n (KK O) W) (M : Submodule O W) (hM : UZStable (O := O) E M)
    (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a b : Fin n) (hab : a ≠ b) (k : ℕ)
    (f : L →ₗ[KK O] W) (hf : f ∈ homLattice M L) :
    divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f ∈ homLattice M L := by
  have hf' : ∀ y : L, (y : W) ∈ M → f y ∈ M := hf
  show ∀ x : L, (x : W) ∈ M → divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f x ∈ M
  intro x hx
  have hexp : divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f x =
      ∑ m ∈ range (k + 1), (((-1 : ℤ) ^ (k - m) : ℤ) : KK O) •
        divPowE E a b m (f ((((k - m).factorial : KK O)⁻¹) • ((restrictRepresentation E L hL a b) ^ (k - m)) x)) := by
    rw [divPowE, LinearMap.smul_apply, LinearMap.smul_apply, homRepresentation_pow_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    simp only [divPowE, LinearMap.smul_apply, map_smul, smul_smul]
    congr 1
    have hc : ((k.choose m : ℕ) : KK O) * (m.factorial : KK O) * ((k - m).factorial : KK O) =
        (k.factorial : KK O) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmk
    have h1 : (m.factorial : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    have h2 : ((k - m).factorial : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (k - m))
    rw [← hc]
    have h3 : ((k.choose m : ℕ) : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hmk).ne'
    push_cast
    field_simp
  rw [hexp]
  refine Submodule.sum_mem _ fun m _ => ?_
  apply int_smul_mem_lattice
  have hy : (((((k - m).factorial : KK O)⁻¹) • ((restrictRepresentation E L hL a b) ^ (k - m)) x : L) : W) =
      divPowE E a b (k - m) (x : W) := by
    rw [Submodule.coe_smul, restrictRepresentation_pow_coe, divPowE, LinearMap.smul_apply]
  have hyM : divPowE E a b (k - m) (x : W) ∈ M := hM _ (Or.inl ⟨a, b, k - m, hab, rfl⟩) _ hx
  have hfy := hf' _ (by rw [hy]; exact hyM)
  exact hM _ (Or.inl ⟨a, b, m, hab, rfl⟩) _ hfy

end lat

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section lat
variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

theorem homLattice_binomial_stable [CharZero (KK O)] [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W) (hE : IsGLRep E)
    (M : Submodule O W) (hM : UZStable (O := O) E M)
    (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a : Fin n) (k : ℕ)
    (f : L →ₗ[KK O] W) (hf : f ∈ homLattice M L) :
    binomE (homRepresentation (restrictRepresentation E L hL) E) a k f ∈ homLattice M L := by
  have hres := restrictRepresentation_isRep E hE L hL
  obtain ⟨s, π, h1, h2, h3, h4, h5⟩ := weight_projections_exist (restrictRepresentation E L hL) hres
  obtain ⟨s', π', h1', h2', h3', h4', h5'⟩ := weight_projections_exist E hE
  have hdec : f = ∑ mu' ∈ s', ∑ mu ∈ s, (π' mu' ∘ₗ f ∘ₗ π mu) := by
    ext x
    simp only [LinearMap.sum_apply, LinearMap.comp_apply]
    have : ∀ mu' ∈ s', ∑ mu ∈ s, π' mu' (f (π mu x)) = π' mu' (f x) := by
      intro mu' _
      rw [← map_sum, ← map_sum, h5]
    rw [Finset.sum_congr rfl this, h5']
  have hwt : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ weightSp (homRepresentation (restrictRepresentation E L hL) E) (mu' - mu) := by
    intro mu' mu
    rw [mem_weightSp_iff_diagonal_apply]
    intro c
    ext x
    simp only [homRepresentation_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      (mem_weightSp_iff_diagonal_apply E mu' _).1 (h4' mu' _) c, weightProjection_diagonal_apply_eq_smul _ hres mu (π mu) (h1 mu) c x, map_smul,
      Pi.sub_apply, Int.cast_sub, sub_smul, LinearMap.sub_apply]
  have hcoe : ∀ mu, L.subtype ∘ₗ π mu = π' mu ∘ₗ L.subtype := by
    intro mu
    refine linearMap_ext_on_weightSpaces _ hres _ _ fun nu y hy => ?_
    have hy' : (y : W) ∈ weightSp E nu := (restrict_mem_weightSpace_iff E L hL nu y).1 hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    by_cases h : nu = mu
    · subst h; rw [(h1 nu).1 y hy, (h1' nu).1 _ hy']
    · rw [(h1 mu).2 nu h y hy, (h1' mu).2 nu h _ hy']; rfl
  have hmem : ∀ mu' mu, (π' mu' ∘ₗ f ∘ₗ π mu) ∈ homLattice M L := by
    intro mu' mu x hx
    have hx1 : ((π mu x : L) : W) ∈ M := by
      have := congrArg (fun g : L →ₗ[KK O] W => g x) (hcoe mu)
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
      rw [this]
      exact weightProjection_preserves_lattice E hE M hM mu (π' mu) (h1' mu) _ hx
    exact weightProjection_preserves_lattice E hE M hM mu' (π' mu') (h1' mu') _ (hf _ hx1)
  rw [hdec, map_sum]
  refine Submodule.sum_mem _ fun mu' _ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun mu _ => ?_
  rw [binomial_diagonal_apply_weight _ a (mu' - mu) _ (hwt mu' mu) k]
  exact int_smul_mem_lattice _ _ (hmem mu' mu)

theorem mem_homLattice_iff_basis (M : Submodule O W) (L : Submodule (KK O) W) {d : ℕ} (b : Module.Basis (Fin d) (KK O) L)
    (hbM : ∀ i, ((b i : L) : W) ∈ M)
    (hbc : ∀ x : L, (x : W) ∈ M → ∀ i, ∃ o : O, b.coord i x = algebraMap O (KK O) o) (f : L →ₗ[KK O] W) :
    f ∈ homLattice M L ↔ ∀ i, f (b i) ∈ M := by
  constructor
  · intro hf i
    exact hf (b i) (hbM i)
  · intro hf
    show ∀ x : L, (x : W) ∈ M → f x ∈ M
    intro x hx
    choose o ho using hbc x hx
    have hx' : x = ∑ i, b.coord i x • b i := by
      simp only [Module.Basis.coord_apply]
      exact (b.sum_repr x).symm
    rw [hx', map_sum]
    refine M.sum_mem fun i _ => ?_
    rw [map_smul, ho i, algebraMap_smul]
    exact M.smul_mem (o i) (hf i)

end lat

theorem hom_lattice_dividedPower_stable : HomLatticeDividedPowerStable := by
  intro O _ _ _ _ n W _ _ _ _ _ E hE M hM hMQ L hL
  obtain ⟨d, b, hbM, hbc⟩ := lattice_adapted_basis_exists O W M hM.2 hMQ L
  have hiff := mem_homLattice_iff_basis M L b hbM hbc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro u (⟨a, c, k, hac, rfl⟩ | ⟨a, k, rfl⟩) f hf
    · exact homLattice_dividedPower_stable E M hM.1 L hL a c hac k f hf
    · exact homLattice_binomial_stable E hE M hM.1 L hL a k f hf
  · have : homLattice M L = (Submodule.pi Set.univ fun _ : Fin d => M).map
        ((b.constr (KK O)).toLinearMap.restrictScalars O) := by
      ext f
      rw [hiff]
      constructor
      · intro hf
        exact ⟨fun i => f (b i), fun i _ => hf i, b.constr_self (KK O) f⟩
      · rintro ⟨y, hy, rfl⟩ i
        have : (b.constr (KK O) y) (b i) = y i := b.constr_basis (KK O) y i
        simpa [this] using hy i trivial
    rw [this]
    exact (Submodule.fg_pi fun _ => hM.2).map _
  · rw [eq_top_iff]
    intro f _
    choose a ha hax using fun i => exists_clear_denominators_alt M (f (b i)) (by rw [hMQ]; trivial)
    have hA : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ha i
    have hA1 : algebraMap O (KK O) (∏ i, a i) ≠ 0 := by
      simpa using (IsFractionRing.injective O (KK O)).ne hA
    have h1 : (∏ i, a i) • f ∈ homLattice M L := by
      rw [hiff]
      intro i
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
      rw [LinearMap.smul_apply, hc, mul_comm, mul_smul]
      exact M.smul_mem _ (hax i)
    have h2 : f = (algebraMap O (KK O) (∏ i, a i))⁻¹ • ((∏ i, a i) • f) := by
      rw [← algebraMap_smul (KK O) (∏ i, a i) f, smul_smul, inv_mul_cancel₀ hA1, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

end Formalism.MainNotions.G.GLWeightTheory
end
end

section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section
variable {n : ℕ} {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

theorem equivariant_intertwines_monoid (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T)
    {u : Module.End K V} (hu : u ∈ Umon E) : ∃ u' ∈ Umon E', ∀ y, T (u y) = u' (T y) :=  by
  have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
  clear hu
  induction hu' using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hy
    exact ⟨E' a b, Submonoid.subset_closure ⟨(a, b), rfl⟩, fun z => hT a b z⟩
  | one => exact ⟨1, one_mem _, fun z => rfl⟩
  | mul y z _ _ hy hz =>
    obtain ⟨y', hy', hy''⟩ := hy
    obtain ⟨z', hz', hz''⟩ := hz
    refine ⟨y' * z', mul_mem hy' hz', fun w => ?_⟩
    show T (y (z w)) = y' (z' (T w))
    rw [hy'', hz'']

theorem equivariant_image_highest_vector (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T)
    (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (h0 : T v ≠ 0) : IsHWV E' mu (T v) :=  by
  obtain ⟨hv0, hvw, hvh⟩ := hv
  refine ⟨h0, ?_, fun a b hab => ?_⟩
  · rw [mem_weightSp_iff_diagonal_apply] at hvw ⊢
    intro a
    rw [← hT, hvw a, map_smul]
  · rw [← hT, hvh a b hab, map_zero]

theorem equivariant_maps_isotypic (E : GLOps n K V) (E' : GLOps n K V') (T : V →ₗ[K] V') (hT : IsEquivariantMap E E' T)
    (mu : Fin n → ℤ) : ∀ x ∈ isoSub E mu, T x ∈ isoSub E' mu :=  by
  intro x hx
  have hle : isoSub E mu ≤ (isoSub E' mu).comap T := by
    unfold isoSub
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    obtain ⟨u', hu', hT'⟩ := equivariant_intertwines_monoid E E' T hT hu
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rw [hT']
    by_cases h0 : T v = 0
    · rw [h0, map_zero]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨u', hu', T v, equivariant_image_highest_vector E E' T hT mu v hv h0, rfl⟩
  exact hle hx

theorem highest_vector_mem_isotypic (E : GLOps n K V) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) : v ∈ isoSub E mu := by
  unfold isoSub
  exact Submodule.subset_span ⟨1, one_mem _, v, hv, rfl⟩

end

private theorem E_apply_mem_weightSp_add_rootW_of_isGLRep {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (hE : IsGLRep E) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) (a b : Fin n) :
    E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [mem_weightSp_iff_diagonal_apply] at hx ⊢
  intro c
  have h1 := congrArg (fun F : Module.End K V => F x) (hE.1 c c a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at h1
  rw [sub_eq_iff_eq_add] at h1
  rw [h1]
  simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  rcases eq_or_ne c a with rfl | hca <;> rcases eq_or_ne c b with rfl | hcb
  · simp
  · simp [hcb, hcb.symm, add_smul]
    abel
  · simp [hca, add_smul]
    abel
  · simp [hca, hcb, hcb.symm]

private theorem E_apply_mem_isoSub_of_mem {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) : ∀ x ∈ isoSub E mu, E a b x ∈ isoSub E mu := by
  intro x hx
  have hle : isoSub E mu ≤ (isoSub E mu).comap (E a b) := by
    unfold isoSub
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    exact Submodule.subset_span ⟨E a b * u, mul_mem (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, v, hv, rfl⟩
  exact hle hx

theorem isotypic_submodules_span_top (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : IsotypicSubmodulesSpanTop := by
  classical
  intro n K V _ _ _ _ _ E hE
  set S : Submodule K V := ⨆ mu, isoSub E mu with hSdef
  have hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S := by
    intro a b x hx
    refine Submodule.iSup_induction (fun mu => isoSub E mu) (motive := fun x => E a b x ∈ S) hx ?_ ?_ ?_
    · intro mu y hy
      exact (le_iSup (fun mu => isoSub E mu) mu) (E_apply_mem_isoSub_of_mem E mu a b y hy)
    · rw [map_zero]
      exact S.zero_mem
    · intro y z hy hz
      rw [map_add]
      exact S.add_mem hy hz
  obtain ⟨W', hc, hW'⟩ := h2 K V n E hE S hS
  have hW'bot : W' = ⊥ := by
    by_contra hne
    obtain ⟨s, π, hπ, hπW, hbot, hπwt, hsum⟩ := weight_projections_exist E hE
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    let T : Finset (Fin n → ℤ) := s.filter (fun mu => ∃ y ∈ W', y ≠ 0 ∧ y ∈ weightSp E mu)
    have hT : T.Nonempty := by
      by_contra hTe
      rw [Finset.not_nonempty_iff_eq_empty] at hTe
      apply hw0
      rw [← hsum w]
      apply Finset.sum_eq_zero
      intro mu hmu
      by_contra hne0
      have hmT : mu ∈ T := Finset.mem_filter.mpr
        ⟨hmu, π mu w, hπW mu W' (fun a y hy => hW' a a y hy) w hwW, hne0, hπwt mu w⟩
      rw [hTe] at hmT
      exact Finset.notMem_empty _ hmT
    obtain ⟨mu, hmuT, hmin⟩ := T.exists_min_image (fun nu => ∑ i : Fin n, (i.val : ℤ) * nu i) hT
    obtain ⟨hmus, v, hvW, hv0, hvw⟩ := Finset.mem_filter.mp hmuT
    have hhw : IsHWV E mu v := by
      refine ⟨hv0, hvw, fun a b hab => ?_⟩
      by_contra hne1
      have hmem : E a b v ∈ weightSp E (mu + rootW a b) := E_apply_mem_weightSp_add_rootW_of_isGLRep E hE mu v hvw a b
      have hs' : mu + rootW a b ∈ s := by
        by_contra hns
        rw [hbot _ hns] at hmem
        exact hne1 ((Submodule.mem_bot K).mp hmem)
      have hT' : mu + rootW a b ∈ T := Finset.mem_filter.mpr ⟨hs', E a b v, hW' a b v hvW, hne1, hmem⟩
      have hle := hmin _ hT'
      have hcalc : ∑ i : Fin n, (i.val : ℤ) * (mu + rootW a b) i =
          (∑ i : Fin n, (i.val : ℤ) * mu i) + ((a.val : ℤ) - b.val) := by
        simp [rootW, Pi.single_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have hab' : (a.val : ℤ) < b.val := by exact_mod_cast hab
      rw [hcalc] at hle
      linarith
    have hvS : v ∈ S := (le_iSup (fun mu => isoSub E mu) mu) (highest_vector_mem_isotypic E mu v hhw)
    have hvI : v ∈ S ⊓ W' := ⟨hvS, hvW⟩
    rw [hc.inf_eq_bot] at hvI
    exact hv0 ((Submodule.mem_bot K).mp hvI)
  rw [← hc.sup_eq_top, hW'bot, sup_bot_eq]

private theorem E_apply_eq_zero_of_isHWV_zero {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (v : V) (hv : IsHWV E 0 v) (a b : Fin n) :
    E a b v = 0 := by
  obtain ⟨hv0, hvw, hvh⟩ := hv
  have hvw' : ∀ c, E c c v = 0 := fun c => by rw [(mem_weightSp_iff_diagonal_apply E 0 v).mp hvw c]; simp
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact hvh a b hab
  · exact hvw' a
  have hne : a ≠ b := ne_of_gt hab
  have r1 : ∀ y, E b a (E a b y) = E a b (E b a y) + (E b b y - E a a y) := by
    intro y
    have h1 := congrArg (fun F : Module.End K V => F y) (hE.1 b a a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true] at h1
    rw [← h1]
    abel
  have r2 : ∀ y, E b b (E a b y) = E a b (E b b y) - E a b y := by
    intro y
    have h1 := congrArg (fun F : Module.End K V => F y) (hE.1 b b a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, if_neg hne.symm, zero_sub,
      LinearMap.neg_apply] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1]
    abel
  have r3 : ∀ y, E a a (E a b y) = E a b (E a a y) + E a b y := by
    intro y
    have h1 := congrArg (fun F : Module.End K V => F y) (hE.1 a a a b)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, if_true, if_neg hne.symm, sub_zero] at h1
    rw [sub_eq_iff_eq_add] at h1
    rw [h1]
    abel
  have hpow : ∀ (k : ℕ) (y : V), (E a b ^ (k + 1)) y = E a b ((E a b ^ k) y) := fun k y => by
    rw [pow_succ']
    rfl
  have H : ∀ k : ℕ, E b b ((E a b ^ k) v) - E a a ((E a b ^ k) v) = (-(2 * (k : K))) • (E a b ^ k) v := by
    intro k
    induction k with
    | zero => simp [hvw']
    | succ k ih =>
      rw [hpow, r2, r3]
      have e1 : E a b (E b b ((E a b ^ k) v)) - E a b ((E a b ^ k) v) -
          (E a b (E a a ((E a b ^ k) v)) + E a b ((E a b ^ k) v)) =
          E a b (E b b ((E a b ^ k) v) - E a a ((E a b ^ k) v)) - (2 : K) • E a b ((E a b ^ k) v) := by
        rw [map_sub, two_smul]
        abel
      rw [e1, ih, map_smul, ← sub_smul]
      congr 1
      push_cast
      ring
  have Ek : ∀ k : ℕ, E b a ((E a b ^ (k + 1)) v) = (-(((k : K) + 1) * k)) • (E a b ^ k) v := by
    intro k
    induction k with
    | zero =>
      rw [hpow, r1]
      simp [hvh b a hab, hvw']
    | succ k ih =>
      rw [hpow (k + 1), r1, ih, H (k + 1), map_smul, ← hpow k, ← add_smul]
      congr 1
      push_cast
      ring
  by_contra hfv
  have hall : ∀ k, (E a b ^ k) v ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using hv0
    | succ k ih =>
      intro h0
      cases k with
      | zero =>
        apply hfv
        simpa using h0
      | succ m =>
        have h1 := Ek (m + 1)
        rw [h0, map_zero] at h1
        have hc : (-((((m + 1 : ℕ) : K) + 1) * ((m + 1 : ℕ) : K))) ≠ 0 := by
          have h2 : ((m + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
          have h3 : ((m + 1 : ℕ) : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
          exact neg_ne_zero.mpr (mul_ne_zero h3 h2)
        exact ih ((smul_eq_zero.mp h1.symm).resolve_left hc)
  have heig : ∀ k : ℕ, (E b b - E a a).HasEigenvector (-(2 * (k : K))) ((E a b ^ k) v) := by
    intro k
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, LinearMap.sub_apply]
    exact ⟨H k, hall k⟩
  have hinj : Function.Injective (fun k : ℕ => -(2 * (k : K))) := by
    intro k j hkj
    simpa using hkj
  have hli := Module.End.eigenvectors_linearIndependent' (E b b - E a a) (fun k : ℕ => -(2 * (k : K))) hinj
    (fun k => (E a b ^ k) v) heig
  have := hli.finite
  exact not_finite ℕ

theorem isotypic_zero_killed_by_operators {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (E : GLOps n K V) (hE : IsGLRep E) (x : V) (hx : x ∈ isoSub E 0) (a b : Fin n) : E a b x = 0 :=  by
  have hle : isoSub E 0 ≤ LinearMap.ker (E a b) := by
    unfold isoSub
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, rfl⟩
    have hP : u v = v ∨ u v = 0 := by
      have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
      clear hu
      induction hu' using Submonoid.closure_induction with
      | mem y hy =>
        obtain ⟨⟨c, d⟩, rfl⟩ := hy
        exact Or.inr (E_apply_eq_zero_of_isHWV_zero E hE v hv c d)
      | one => exact Or.inl rfl
      | mul y z _ _ hy hz =>
        rcases hz with hz | hz
        · show y (z v) = v ∨ y (z v) = 0
          rw [hz]
          exact hy
        · right
          show y (z v) = 0
          rw [hz, map_zero]
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rcases hP with h | h <;> rw [h]
    · exact E_apply_eq_zero_of_isHWV_zero E hE v hv a b
    · exact map_zero _
  exact hle hx

theorem invariant_projection_exists (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : InvariantProjectionExists :=  by
  intro n K V _ _ _ _ _ E hE
  set Inv : Submodule K V := ⨅ a, ⨅ b, LinearMap.ker (E a b) with hInvdef
  have hInvmem : ∀ x, x ∈ Inv ↔ ∀ a b, E a b x = 0 := by
    intro x
    simp [Inv, Submodule.mem_iInf]
  have hInvS : ∀ a b, ∀ x ∈ Inv, E a b x ∈ Inv := by
    intro a b x hx
    rw [(hInvmem x).mp hx a b]
    exact Inv.zero_mem
  obtain ⟨W', hc, hW'⟩ := h2 K V n E hE Inv hInvS
  refine ⟨Inv.projection W' hc, ?_⟩
  have hPE : ∀ c d y, Inv.projection W' hc (E c d y) = 0 := by
    intro c d y
    have hy := Submodule.projection_add_projection_eq_self hc y
    rw [← hy, map_add, (hInvmem _).mp (Submodule.projection_apply_mem hc y) c d, zero_add]
    exact (Submodule.projection_apply_eq_zero_iff hc).mpr
      (hW' c d _ (Submodule.projection_apply_mem hc.symm y))
  unfold IsInvProj IsIsoProj
  refine ⟨fun x hx => ?_, fun mu hmu x hx => ?_⟩
  · exact Submodule.projection_apply_of_mem_left hc ((hInvmem x).mpr (fun a b => isotypic_zero_killed_by_operators E hE x hx a b))
  · have hle : isoSub E mu ≤ LinearMap.ker (Inv.projection W' hc) := by
      unfold isoSub
      rw [Submodule.span_le]
      rintro y ⟨u, hu, v, hv, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      have hQ : u = 1 ∨ ∀ z, Inv.projection W' hc (u z) = 0 := by
        have hu' : u ∈ Submonoid.closure (Set.range fun ab : Fin n × Fin n => E ab.1 ab.2) := hu
        clear hu
        induction hu' using Submonoid.closure_induction with
        | mem y hy =>
          obtain ⟨⟨c, d⟩, rfl⟩ := hy
          exact Or.inr (hPE c d)
        | one => exact Or.inl rfl
        | mul y z _ _ hy hz =>
          rcases hy with rfl | hy
          · rw [one_mul]
            exact hz
          · right
            intro w
            exact hy (z w)
      rcases hQ with rfl | hQ
      · obtain ⟨c, hc0⟩ : ∃ c, mu c ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hmu (funext hcon)
        have hvw := (mem_weightSp_iff_diagonal_apply E mu v).mp hv.2.1 c
        have hK : (mu c : K) ≠ 0 := Int.cast_ne_zero.mpr hc0
        have hv' : v = ((mu c : K))⁻¹ • E c c v := by
          rw [hvw, smul_smul, inv_mul_cancel₀ hK, one_smul]
        rw [Module.End.one_apply, hv', map_smul, hPE, smul_zero]
      · exact hQ v
    exact hle hx

theorem equivariant_commutes_isotypic (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : EquivariantCommutesInvariantProjection :=  by
  intro n K V V' _ _ _ _ _ _ _ _ E E' hE hE' T hT P P' hP hP' x
  have htop := isotypic_submodules_span_top D h2 n K V E hE
  have hx : x ∈ ⨆ mu, isoSub E mu := by
    rw [htop]
    trivial
  refine Submodule.iSup_induction (fun mu => isoSub E mu) (motive := fun x => T (P x) = P' (T x)) hx ?_ ?_ ?_
  · intro mu y hy
    by_cases hmu : mu = 0
    · subst hmu
      rw [hP.1 y hy, hP'.1 (T y) (equivariant_maps_isotypic E E' T hT 0 y hy)]
    · rw [hP.2 mu hmu y hy, map_zero, hP'.2 mu hmu (T y) (equivariant_maps_isotypic E E' T hT mu y hy)]
  · simp
  · intro y z hy hz
    simp only [map_add]
    rw [hy, hz]

theorem invariant_projection_range_trivial (D : Formalism.BasicNotions.D7) (h2 : adm2 D) {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (E : GLOps n K V) (hE : IsGLRep E) (P : Module.End K V)
    (hP : IsInvProj E P) (x : V) : P x ∈ isoSub E 0 :=  by
  have htop := isotypic_submodules_span_top D h2 n K V E hE
  have hx : x ∈ ⨆ mu, isoSub E mu := by
    rw [htop]
    trivial
  refine Submodule.iSup_induction (fun mu => isoSub E mu) (motive := fun x => P x ∈ isoSub E 0) hx ?_ ?_ ?_
  · intro mu y hy
    by_cases hmu : mu = 0
    · subst hmu
      rw [hP.1 y hy]
      exact hy
    · rw [hP.2 mu hmu y hy]
      exact Submodule.zero_mem _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

theorem invariant_projection_kills_operators (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : OperatorsKillInvariantProjection := by
  intro n K V _ _ _ _ _ E hE P hP x a b
  exact isotypic_zero_killed_by_operators E hE _ (invariant_projection_range_trivial D h2 E hE P hP x) a b

end Formalism.MainNotions.G.GLWeightTheory
end
end
