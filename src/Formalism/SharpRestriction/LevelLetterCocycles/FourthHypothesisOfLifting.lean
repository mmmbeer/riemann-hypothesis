import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO

noncomputable section

namespace Formalism.MainNotions.PairedCharacterCondition.RT

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Polynomial CategoryTheory Formalism.MainNotions.PairedCharacterCondition

section Reps

open Formalism.IrreducibleCountingLemmas.TYPES (RepIso)

variable {Γ : Type} [Group Γ]

variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]




end Reps

section Blocks

open Formalism.IrreducibleCountingLemmas.TYPES

theorem twoBlock_eq_zero {n a : ℕ} (i : Fin n) : twoBlock n a i = 0 ↔ (i : ℕ) < a := by
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

theorem twoBlock_eq_one {n a : ℕ} (i : Fin n) : twoBlock n a i = 1 ↔ a ≤ (i : ℕ) := by
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]
  split_ifs with h
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h (by omega)⟩
  · exact ⟨fun _ => by omega, fun _ => rfl⟩


def blk0 (a b : ℕ) : {i : Fin (a + b) // twoBlock (a + b) a i = 0} ≃ Fin a where
  toFun i := ⟨i.1, (twoBlock_eq_zero i.1).1 i.2⟩
  invFun j := ⟨⟨j, by omega⟩, (twoBlock_eq_zero _).2 j.2⟩
  left_inv i := by rcases i with ⟨⟨i, hi⟩, h⟩; rfl
  right_inv j := by rcases j with ⟨j, hj⟩; rfl

def blk1 (a b : ℕ) : {i : Fin (a + b) // twoBlock (a + b) a i = 1} ≃ Fin b where
  toFun i := ⟨i.1 - a, by have := (twoBlock_eq_one i.1).1 i.2; have := i.1.2; omega⟩
  invFun j := ⟨⟨a + j, by omega⟩, (twoBlock_eq_one _).2 (by simp)⟩
  left_inv i := by
    rcases i with ⟨⟨i, hi⟩, h⟩
    have hai : a ≤ i := (twoBlock_eq_one _).1 h
    apply Subtype.ext
    apply Fin.ext
    show a + (i - a) = i
    omega
  right_inv j := by
    rcases j with ⟨j, hj⟩
    apply Fin.ext
    simp

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def pairRep {a b : ℕ} (ρ : FDRep ℂ (GL (Fin a) K)) (ρ' : FDRep ℂ (GL (Fin b) K)) :
    ∀ c : Fin 2, FDRep ℂ (GL {i : Fin (a + b) // twoBlock (a + b) a i = c} K)
  | 0 => transp (blk0 a b).symm ρ
  | 1 => transp (blk1 a b).symm ρ'


end Blocks

section Comparison₂

open Formalism.IrreducibleCountingLemmas.TYPES

def castIrr {g : ℕ} (L : LzData g) {a a' : ℕ} (h : a = a') (τ : L.Irr a) : L.Irr a' := h ▸ τ



structure LzTie {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C)
    (L : LzData g) where
  rep : ∀ {a : ℕ}, L.Irr a → FDRep ℂ (GL (Fin a) (ZMod g))
  rep_simple : ∀ {a : ℕ} (τ : L.Irr a), Simple (rep τ)
  rep_inj : ∀ {a : ℕ} (τ σ : L.Irr a), RepIso (rep τ).ρ (rep σ).ρ → τ = σ
  rep_surj : ∀ {a : ℕ} (σ : FDRep ℂ (GL (Fin a) (ZMod g))), Simple σ → ∃ τ, RepIso σ.ρ (rep τ).ρ
  idem_eq : ∀ {a : ℕ} (τ : L.Irr a), L.idem τ = zIdem (rep τ)
  lab_eq : ∀ {a : ℕ} (τ : L.Irr a), 1 ≤ a → HasLabelO O (rep τ) (L.lab τ)
  real : ∀ {a : ℕ}, L.Rep a → FDRep ℂ (GL (Fin a) (ZMod g))
  real_ext : ∀ {a : ℕ} (R R' : L.Rep a), RepIso (real R).ρ (real R').ρ → R = R'
  real_ofIrr : ∀ {a : ℕ} (τ : L.Irr a), RepIso (real (L.ofIrr τ)).ρ (rep τ).ρ
  cons_iff : ∀ {a : ℕ} (R : L.Rep a) (σ : L.Irr a), L.cons R σ ↔ IsConstituent (rep σ) (real R).ρ
  real_hc : ∀ {a b : ℕ} (τ : L.Irr a) (τ' : L.Irr b), 1 ≤ a → 1 ≤ b →
    RepIso (real (L.hc τ τ')).ρ (hcRep (ZMod g) (twoBlock (a + b) a) (pairRep (rep τ) (rep τ')))
  hc_zero_left : ∀ {b : ℕ} (τ : L.Irr 0) (τ' : L.Irr b),
    L.hc τ τ' = L.ofIrr (castIrr L (Nat.zero_add b).symm τ')
  hc_zero_right : ∀ {a : ℕ} (τ : L.Irr a) (τ' : L.Irr 0), L.hc τ τ' = L.ofIrr τ

end Comparison₂

section HC

open Formalism.IrreducibleCountingLemmas.TYPES

def HCBody {g : ℕ} (L : LzData g) : Prop :=
  ∀ (a b : ℕ) (τ : L.Irr a) (τ' : L.Irr b),
    (∀ σ, L.cons (L.hc τ τ') σ → L.lab σ = L.lab τ * L.lab τ') ∧
    (IsCoprime (L.lab τ) (L.lab τ') →
      (∃ σ, L.hc τ τ' = L.ofIrr σ) ∧
      ∀ (τ₁ : L.Irr a) (τ₁' : L.Irr b), L.lab τ₁ = L.lab τ →
        L.lab τ₁' = L.lab τ' → L.hc τ₁ τ₁' = L.hc τ τ' → τ₁ = τ ∧ τ₁' = τ')


theorem lab_zero {g : ℕ} (L : LzData g) (τ : L.Irr 0) : L.lab τ = 1 := by
  first
  | exact (L.lab_spec τ).1.natDegree_eq_zero_iff_eq_one.1 (L.lab_spec τ).2.1
  | exact Polynomial.eq_one_of_monic_natDegree_zero (L.lab_spec τ).1 (L.lab_spec τ).2.1



variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} {O : LabelMap (ZMod g) C} {L : LzData g}


end HC

section Row

open Formalism.IrreducibleCountingLemmas.TYPES

variable {D : D7}

def AdmHarishChandraTypes (P : Pend D) : Prop :=
  ∀ k : Fin 2,
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ (C : LabelConv (ZMod (D.host.g k))) (O : LabelMap (ZMod (D.host.g k)) C),
      Nonempty (LzTie O (P.lz k)) → HCBody (P.lz k)

def TypesHC (g : ℕ) [Fact g.Prime] : Prop :=
  ∀ (C : LabelConv (ZMod g)) (O : LabelMap (ZMod g) C),
    HCLabelO O ∧ LabelMulO O ∧ TranspO O ∧ HCDisjointO O


def LzCompatibility (P : Pend D) : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ (C : LabelConv (ZMod (D.host.g k))) (O : LabelMap (ZMod (D.host.g k)) C),
      Nonempty (LzTie O (P.lz k))



end Row

section Refute

open Formalism.IrreducibleCountingLemmas.TYPES

theorem irr_nonempty {g : ℕ} (L : LzData g) (a : ℕ) : Nonempty (L.Irr a) := by
  by_contra hne
  have h0 : ∑ τ : L.Irr a, L.idem τ = 0 :=
    Finset.sum_eq_zero (fun τ _ => absurd (Nonempty.intro τ) hne)
  exact one_ne_zero ((L.idem_sum a).symm.trans h0)

theorem spec_XsubC {g : ℕ} [Fact g.Prime] (c : ZMod g) (hc : c ≠ 0) (n : ℕ) :
    ((X - C c) ^ n).Monic ∧ ((X - C c) ^ n).natDegree = n ∧ ((X - C c) ^ n).coeff 0 ≠ 0 := by
  refine ⟨(Polynomial.monic_X_sub_C c).pow n, ?_, ?_⟩
  · first
    | rw [(Polynomial.monic_X_sub_C c).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    | simp
  · rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    exact pow_ne_zero _ (neg_ne_zero.2 hc)

def relabel {g : ℕ} [Fact g.Prime] (h2 : (2 : ZMod g) ≠ 0) (L : LzData g) : LzData g where
  Irr := L.Irr
  idem := L.idem
  idem_idem := L.idem_idem
  idem_central := L.idem_central
  idem_ne := L.idem_ne
  idem_orth := L.idem_orth
  idem_sum := L.idem_sum
  idem_prim := L.idem_prim
  lab := fun {a} τ => if a = 1 then (X - C 1) ^ 1 else if a = 2 then (X - C 2) ^ 2 else L.lab τ
  lab_spec := by
    intro a τ
    by_cases h1 : a = 1
    · subst h1; simpa using spec_XsubC (1 : ZMod g) one_ne_zero 1
    · by_cases h2' : a = 2
      · subst h2'; simpa using spec_XsubC (2 : ZMod g) h2 2
      · simpa [h1, h2'] using L.lab_spec τ
  Rep := L.Irr
  ofIrr := fun τ => τ
  cons := fun R σ => σ = R
  cons_ofIrr := fun _ _ => Iff.rfl
  hc := fun {a b} _ _ => Classical.choice (irr_nonempty L (a + b))



end Refute

section DZ

variable {D : D7}

def Occurs (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k)
    (z : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) : Prop :=
  ∃ F ∈ D.naut.typeV i PI, D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) F ≠ 0

def DZConcl (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (PI : D.naut.AV i)
    (f : (ZMod (D.host.g k))[X]) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∃ u : (ZMod (D.host.g k))ˣ, (u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹) ∧
    D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) ∧
    D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)) =
      f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t ∧
    ∀ w', IsConjPl D.host (D.naut.plGw k v) w' →
      D.naut.mono0 (D.naut.locV i PI w') ∧
      (D.naut.items₂ k w' (D.naut.locV i PI w')).natDegree = D.R.nV ∧
      Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
        (Formalism.CyclotomicNorms.rootsBar (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹)

def AdmDepthZeroTypes : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (PI : D.naut.AV i),
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∀ (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k)))) (f : (ZMod (D.host.g k))[X]),
      Simple ρ → Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ * D.ntypes.eSer k f = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ →
      Occurs i PI k v (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) → Squarefree f →
      (∀ u : (ZMod (D.host.g k))ˣ, u = chiJ D i k v ∨ u = (chiJ D i k v)⁻¹ →
        ¬ f.IsRoot (u : ZMod (D.host.g k))) →
      DZConcl i k v PI f

def KtyTie (P : Pend D) : Prop :=
  ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (τ : (P.lz k).Irr D.R.r),
    τ ∈ P.kty i PI k v → Occurs i PI k v ((P.lz k).idem τ)

theorem ktyTie_of_spec (P : Pend D) : KtyTie P := by
  intro i PI k v τ hτ
  exact (P.kty_spec i PI k v τ).1 hτ

theorem idem_mul_eSer (P : Pend D) (k : Fin 2) (τ : (P.lz k).Irr D.R.r) :
    (P.lz k).idem τ * D.ntypes.eSer k ((P.lz k).lab τ) = (P.lz k).idem τ := by
  rw [P.eSer_eq, Finset.mul_sum, Finset.sum_eq_single τ]
  · rw [if_pos rfl, (P.lz k).idem_idem τ]
  · intro σ _ hne
    split_ifs
    · exact (P.lz k).idem_orth τ σ (fun h => hne h.symm)
    · exact mul_zero _
  · intro h
    exact absurd (Finset.mem_univ τ) h



end DZ

section TY

open Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

end TY

end Formalism.MainNotions.PairedCharacterCondition.RT

end
