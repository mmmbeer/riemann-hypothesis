import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DepthZeroGoodLines
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.TypeDim

section Finite

variable {F : Type} [Field F] {N : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
  [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def IsCuspLevi (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W) : Prop :=
  ∀ c : Fin N → ℕ, (∃ i j, b i = b j ∧ c i ≠ c j) → ∀ x : W,
    (∀ m : Parabolic.levi F b, (m : GL (Fin N) F) ∈ FiniteGL.unipRadical F c → μ m x = x) → x = 0

def Conj (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W)
    (b' : Fin N → ℕ) (μ' : Representation ℂ (Parabolic.levi F b') W') : Prop :=
  ∃ w : Equiv.Perm (Fin N), (∀ i j, b' (w i) = b' (w j) ↔ b i = b j) ∧ ∃ φ : W ≃ₗ[ℂ] W',
    ∀ (m : Parabolic.levi F b) (m' : Parabolic.levi F b') (x : W),
      (m' : GL (Fin N) F) = Parabolic.permGL F w * m * (Parabolic.permGL F w)⁻¹ → φ (μ m x) = μ' m' (φ x)

def Link (τ : Representation ℂ (GL (Fin N) F) V) (τ' : Representation ℂ (GL (Fin N) F) V') : Prop :=
  ∃ (b : Fin N → ℕ) (φ : (Parabolic.hcRes b τ).IntertwiningMap (Parabolic.hcRes b τ')), φ ≠ 0

def Occurs (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W)
    (τ : Representation ℂ (GL (Fin N) F) V) : Prop :=
  Parabolic.Embeds μ (Parabolic.hcRes b τ)

end Finite

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev part (r t : ℕ) := two (stdSum (rfl : r + t = r + t))

abbrev LiftSp (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Type :=
  IndSp (part r t) ((extTensor (twist σ (detChar (Fin r) (χW * χV⁻¹))) (detRep (Fin t) χW)).comp
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)

def evAt (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) (g : GL (Fin (r + t)) k) :
    LiftSp t σ χW χV →ₗ[ℂ] V where
  toFun f := TensorProduct.rid ℂ V (f.1.1 g)
  map_add' f f' := map_add (TensorProduct.rid ℂ V) (f.1.1 g) (f'.1.1 g)
  map_smul' c f := map_smul (TensorProduct.rid ℂ V) c (f.1.1 g)

variable {σ : Representation ℂ (GL (Fin r) k) V} {χW χV : kˣ →* ℂˣ}

theorem evAt_apply (g : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV) :
    evAt t σ χW χV g f = TensorProduct.rid ℂ V (f.1.1 g) := rfl









def diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : GL (Fin (r + t)) 𝒪[k] :=
  emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (a, d)

theorem diagO_ul (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin r) :
    (diagO a d).val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_lr (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin t) :
    (diagO a d).val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ll (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin t) (j : Fin r) :
    (diagO a d).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ur (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin r) (j : Fin t) :
    (diagO a d).val (Fin.castAdd t i) (Fin.natAdd r j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem hasBlocks_diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : HasBlocks (diagO a d) a d := by
  refine ⟨diagO_ul a d, diagO_lr a d, fun i j => ?_⟩
  rw [diagO_ll]
  exact Ideal.zero_mem _

theorem incl_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (incl k n a).val i j = (a.val i j : k) := rfl

theorem red_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (red k n a).val i j = IsLocalRing.residue 𝒪[k] (a.val i j) := rfl

theorem incl_diagO_one (a : GL (Fin r) 𝒪[k]) : incl k (r + t) (diagO a 1) = diagOne k r t a := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [incl_val]
  simp only [diagO, diagOne, MonoidHom.comp_apply, MonoidHom.inl_apply, val_emb₂, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  generalize (stdSum (rfl : r + t = r + t)).symm i = x
  generalize (stdSum (rfl : r + t = r + t)).symm j = y
  rcases x with x | x <;> rcases y with y | y <;> simp [incl_val, Matrix.one_apply, apply_ite]

theorem red_surjective (n : ℕ) : Function.Surjective (red k n) := by
  intro g
  let M : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j =>
    Function.surjInv (IsLocalRing.residue_surjective (R := 𝒪[k])) (g.val i j)
  have hM : M.map (IsLocalRing.residue 𝒪[k]) = g.val := by
    ext i j
    exact Function.surjInv_eq (IsLocalRing.residue_surjective (R := 𝒪[k])) _
  have hdet : IsUnit M.det := by
    apply IsUnit.of_map (IsLocalRing.residue 𝒪[k])
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact Matrix.isUnits_det_units g
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).mpr hdet).unit, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [red_val]
  exact Function.surjInv_eq (IsLocalRing.residue_surjective (R := 𝒪[k])) _



def Nice (r t : ℕ) (w : Equiv.Perm (Fin (r + t))) (S : Finset (Fin r)) : Prop :=
  (∀ i, i ∉ S → w (Fin.castAdd t i) = Fin.castAdd t i) ∧
  (∀ i ∈ S, r ≤ (w (Fin.castAdd t i) : ℕ) ∧ r ≤ (w.symm (Fin.castAdd t i) : ℕ)) ∧ (S = ∅ → w = 1)


end Local

end GlobalTheory.TypeDim
