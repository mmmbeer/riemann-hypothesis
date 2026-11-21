import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses

section Finite

variable {F : Type} [Field F] {n : ℕ} {Y : Type} [AddCommGroup Y] [Module ℂ Y]

def IsCuspFin (τ : Representation ℂ (GL (Fin n) F) Y) : Prop :=
  ∀ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad F e ≠ ⊥ →
    Subsingleton (Jacquet τ (unipRad F e))

def hcInd {s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {X : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) F) (X a)) :=
  ind (parab F e) ((piTensor ρ).comp (leviProj F e))

def IsSuppFin (τ : Representation ℂ (GL (Fin n) F) Y) {s : ℕ} (d : Fin s → ℕ) {X : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) F) (X a)) : Prop :=
  τ.IsIrreducible ∧ (∀ a, 0 < d a ∧ (ρ a).IsIrreducible ∧ IsCuspFin (ρ a)) ∧
    ∃ e : (Σ a, Fin (d a)) ≃ Fin n, IsSubquotient τ (hcInd e ρ)

def SameClass {m : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ₁ : Representation ℂ (GL (Fin m) F) X) (ρ₂ : Representation ℂ (GL (Fin n) F) Y) : Prop :=
  ∃ (h : m = n) (φ : X ≃ₗ[ℂ] Y), ∀ (g : GL (Fin m) F) (x : X),
    φ (ρ₁ g x) = ρ₂ (h ▸ g : GL (Fin n) F) (φ x)

def superSum (u : Matrix (Fin n) (Fin n) F) : F :=
  ∑ i : Fin n, ∑ j : Fin n, if (j : ℕ) = i + 1 then u i j else 0

theorem superSum_mul (u v : unipB F (Fin n)) :
    superSum ((u * v : unipB F (Fin n)) : GL (Fin n) F).val =
      superSum (u : GL (Fin n) F).val + superSum (v : GL (Fin n) F).val := by
  obtain ⟨hu, hu1⟩ := (mem_unipB F).1 u.2
  obtain ⟨hv, hv1⟩ := (mem_unipB F).1 v.2
  unfold superSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · show ((u : GL (Fin n) F).val * (v : GL (Fin n) F).val) i j = _
    rw [Matrix.mul_apply, Fintype.sum_eq_add i j (by intro e; rw [e] at h; omega), hu1, hv1]
    · ring
    · rintro l ⟨h1, h2⟩
      rcases lt_or_gt_of_ne h1 with h3 | h3
      · rw [hu i l h3, zero_mul]
      · have h4 : j < l := by
          have a1 : (i : ℕ) < l := h3
          have a2 : (l : ℕ) ≠ j := fun e => h2 (Fin.ext e)
          show (j : ℕ) < l
          omega
        rw [hv l j h4, mul_zero]
  · simp

def genChar (n : ℕ) (ψ₀ : AddChar F ℂ) : unipB F (Fin n) →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun u => ψ₀ (superSum (u : GL (Fin n) F).val)
      map_one' := by
        have : superSum ((1 : unipB F (Fin n)) : GL (Fin n) F).val = 0 := by
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
          split_ifs with h
          · exact Matrix.one_apply_ne (by intro e; rw [e] at h; omega)
          · rfl
        rw [this, AddChar.map_zero_eq_one]
      map_mul' := fun u v => by rw [superSum_mul, AddChar.map_add_eq_mul] }

end Finite

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k :=
  Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)

def red (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) 𝓀[k] :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])

def diagOne (r t : ℕ) : GL (Fin r) 𝒪[k] →* GL (Fin (r + t)) k :=
  (emb₂ k (stdSum (rfl : r + t = r + t))).comp ((MonoidHom.inl _ _).comp (incl k r))

def unipLevel (r : ℕ) : Subgroup (GL (Fin r) 𝒪[k]) := (unipB 𝓀[k] (Fin r)).comap (red k r)

variable {k} {r t n : ℕ} {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

def unipLevelChar (r : ℕ) (ψ₀ : AddChar 𝓀[k] ℂ) : unipLevel k r →* ℂˣ :=
  (genChar r ψ₀).comp ((red k r).subgroupComap _)

def IsLevel (J : Subgroup (GL (Fin r) 𝒪[k])) (lam : J →* ℂˣ) : Prop :=
  (red k r).ker ≤ J ∧ ∀ a : J, red k r a = 1 → lam a = 1

def HasBlocks (h : GL (Fin (r + t)) 𝒪[k]) (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : Prop :=
  (∀ i j, h.val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j) ∧
  (∀ i j, h.val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j) ∧
  ∀ i j, h.val (Fin.natAdd r i) (Fin.castAdd t j) ∈ IsLocalRing.maximalIdeal 𝒪[k]

def typeG (π : Representation ℂ (GL (Fin (r + t)) k) W) (J : Subgroup (GL (Fin r) 𝒪[k]))
    (lam : J →* ℂˣ) (χ : kˣ →* ℂˣ) : Submodule ℂ W where
  carrier := {w | ∀ (h : GL (Fin (r + t)) 𝒪[k]) (a : J) (d : GL (Fin t) 𝒪[k]), HasBlocks h a d →
    π (incl k (r + t) h) w = ((lam a * detChar (Fin t) χ (incl k t d) : ℂˣ) : ℂ) • w}
  add_mem' := by
    intro x y hx hy h a d H
    rw [map_add, hx h a d H, hy h a d H, smul_add]
  zero_mem' := by intro h a d _; simp
  smul_mem' := by
    intro c x hx h a d H
    rw [map_smul, hx h a d H, smul_comm]

def liftRep (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) :=
  prod₂ (twist σ (detChar (Fin r) (χW * χV⁻¹))) (detRep (Fin t) χW)

def IsConstituent (τ : Representation ℂ (GL (Fin r) 𝓀[k]) Y) (π : Representation ℂ (GL (Fin r) 𝒪[k]) W)
    (T : Submodule ℂ W) : Prop :=
  τ.IsIrreducible ∧ ∃ f : Y →ₗ[ℂ] W, Function.Injective f ∧ (∀ y, f y ∈ T) ∧
    ∀ a y, f (τ (red k r a) y) = π a (f y)

def InDepthZero (τ : Representation ℂ (GL (Fin r) 𝓀[k]) Y) (σ : Representation ℂ (GL (Fin r) k) V) :
    Prop :=
  IsConstituent τ (σ.comp (incl k r)) (fixed σ (KOne k (Fin r)))

def IsCharBlock (ρ : Representation ℂ (GL (Fin n) 𝓀[k]) Y) (χ : kˣ →* ℂˣ) : Prop :=
  n = 1 ∧ ∀ (u : GL (Fin n) 𝒪[k]) (y : Y),
    ρ (red k n u) y = (detChar (Fin n) χ (incl k n u) : ℂ) • y

def IsDepthZeroSupp (σ : Representation ℂ (GL (Fin r) k) V) {s : ℕ} (d : Fin s → ℕ) {X : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) 𝓀[k]) (X a)) : Prop :=
  ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (GL (Fin r) 𝓀[k]) Y),
    InDepthZero τ σ ∧ IsSuppFin τ d ρ

def GoodAt (σ : Representation ℂ (GL (Fin r) k) V) (χ : kˣ →* ℂˣ) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (X : Fin s → Type) (_ : ∀ a, AddCommGroup (X a)) (_ : ∀ a, Module ℂ (X a))
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) 𝓀[k]) (X a)),
    IsDepthZeroSupp σ d ρ ∧ (∀ a b, a ≠ b → ¬ SameClass (ρ a) (ρ b)) ∧
      ∀ a, ¬ IsCharBlock (ρ a) χ ∧ ¬ IsCharBlock (ρ a) χ⁻¹

def IsDatum (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Prop :=
  (σ.IsIrreducible ∧ IsSmooth σ ∧ IsUnitarisable σ) ∧
    IsUnitaryChar χW ∧ IsUnitaryChar χV ∧ IsTame χW ∧ IsUnram (χW * χV⁻¹)

end Local

section Places

variable {ι : Type} [Fintype ι] (k : ι → Type) [∀ v, Field (k v)] [∀ v, ValuativeRel (k v)]
  [∀ v, TopologicalSpace (k v)] [∀ v, IsNonarchimedeanLocalField (k v)] (r : ℕ)

variable {k r}

end Places

section Examples

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isDatum_detRep (r : ℕ) {χ χW χV : kˣ →* ℂˣ} (h : IsUnram χ) (hu : IsUnitaryChar χ)
    (hW : IsUnitaryChar χW) (hV : IsUnitaryChar χV) (ht : IsTame χW) (hr : IsUnram (χW * χV⁻¹)) :
    IsDatum (detRep (Fin r) χ) χW χV :=
  ⟨⟨isIrreducible_ofChar _, (isSmooth_ofChar_iff _).2 (isSmoothChar_of_isUnram h).detChar,
    (isUnitarisable_ofChar_iff _).2 fun _ => hu _⟩, hW, hV, ht, hr⟩

example (r : ℕ) : IsDatum (detRep (Fin r) (1 : kˣ →* ℂˣ)) 1 1 :=
  isDatum_detRep r (fun _ _ => rfl) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
    (fun _ _ => rfl) (fun _ _ => by simp)

example (r t : ℕ) : HasBlocks (k := k) (r := r) (t := t) 1 1 1 := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]
  · rw [Units.val_one, Matrix.one_apply_ne]
    · exact zero_mem _
    · intro e
      have := congrArg Fin.val e
      simp at this
      omega

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses
