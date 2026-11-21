import Mathlib
import Formalism.LocalRingCardinality.DataKerP
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns

noncomputable section

namespace Formalism.MainNotions.AlgebraicJets

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

section Ent

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def EntIn (i : ℕ) (S : Set ℂ) : Prop :=
  ∀ a, ∃ t : (M.lat (i + 1)).ι → ℂ, (∀ b, t b ∈ S) ∧
    C.K i (M.emb i ((M.lat i).b a)) = ∑ b, t b • M.emb (i + 1) ((M.lat (i + 1)).b b)

theorem EntIn.mono {i : ℕ} {S S' : Set ℂ} (h : EntIn M i S) (hS : S ⊆ S') : EntIn M i S' := by
  intro a
  obtain ⟨t, ht, he⟩ := h a
  exact ⟨t, fun b => hS (ht b), he⟩

theorem kRat_iff_entIn (i : ℕ) : M.KRat i ↔ EntIn M i (Set.range D.what₂.embLL) := by
  constructor
  · intro h a
    obtain ⟨y, hy⟩ := h ((M.lat i).b a)
    refine ⟨fun b => D.what₂.embLL ((M.lat (i + 1)).b.repr y b), fun b => ⟨_, rfl⟩, ?_⟩
    rw [← hy]
    conv_lhs => rw [← (M.lat (i + 1)).b.sum_repr y]
    rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [LinearMap.map_smulₛₗ]
  · intro h x
    choose t ht hK using h
    choose s hs using ht
    refine ⟨∑ a, (M.lat i).b.repr x a • ∑ b, s a b • (M.lat (i + 1)).b b, ?_⟩
    have h1 : C.K i (M.emb i x) = C.Klin i (M.emb i x) := rfl
    rw [h1]
    conv_rhs => rw [← (M.lat i).b.sum_repr x]
    simp only [map_sum, LinearMap.map_smulₛₗ, map_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : C.Klin i (M.emb i ((M.lat i).b a)) = C.K i (M.emb i ((M.lat i).b a)) := rfl
    rw [h2, hK a]
    simp only [hs]



end Ent

def kRatTw (D : D7) (Tw : TwForms D) : Prop := ∀ u w, ∀ i < D.R.m, (Tw.fm u (D.what₂.muAt w)).KRat i

def LLKer (D : D7) (Tw : TwForms D) : Prop :=
  (∀ u, ∀ i < D.R.m, EntIn (D.fm u) i (Set.range D.what₂.embLL)) ∧
    ∀ u w, ∀ i < D.R.m, EntIn (Tw.fm u (D.what₂.muAt w)) i (Set.range D.what₂.embLL)

theorem llKer_iff (D : D7) (Tw : TwForms D) : LLKer D Tw ↔ kRat D ∧ kRatTw D Tw := by
  unfold LLKer kRatTw StandardLatticesGL3.kRat
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun u i hi => (kRat_iff_entIn _ i).2 (h1 u i hi), fun u w i hi => (kRat_iff_entIn _ i).2 (h2 u w i hi)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun u i hi => (kRat_iff_entIn _ i).1 (h1 u i hi), fun u w i hi => (kRat_iff_entIn _ i).1 (h2 u w i hi)⟩


section Alg

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (O : GL3Theta.LiftObj D C)

def RegIn (i : ℕ) (S : Set ℂ) (f : C.Y i → ℂ) : Prop :=
  ∃ (n : D.what₂.Tau → ℕ) (Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ), (∀ α, MvPolynomial.coeff α Q ∈ S) ∧
    ∀ y, (∏ τ, C.de i y τ ^ n τ) * f y = GL3Theta.evFr D Q (O.frm i y)

def SrcTie (i : ℕ) (dg : D.what₂.Tau → ℕ) : Prop :=
  ∀ a c, ∃ Q : MvPolynomial (GL3Theta.FrV D (D.R.N i)) ℂ, (∀ α, MvPolynomial.coeff α Q ∈ Set.range D.what₂.embLL) ∧ GL3Columns.HomDeg D Q dg ∧
    C.sharp i (M.emb i ((M.lat i).b a) c) = fun y => GL3Theta.evFr D Q (O.frm i y)

def TgtTie (j : ℕ) : Prop :=
  ∀ F : IntermediateField ℚ ℂ, Set.range D.what₂.embLL ⊆ (F : Set ℂ) → ∀ φ ∈ M.Fi j, (∀ c, RegIn O j (F : Set ℂ) (φ c)) →
    ∃ t : (M.lat j).ι → ℂ, (∀ b, t b ∈ F) ∧ φ = ∑ b, t b • M.emb j ((M.lat j).b b)

def KFi (i : ℕ) : Prop := ∀ φ ∈ M.Fi i, C.K i φ ∈ M.Fi (i + 1)

def RhoAlg (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (i : ℕ) : Prop :=
  (∀ c, C.rhoDet i c ∈ Qbar) ∧ ∀ c', C.rhoDet' i c' ∈ Qbar

def Ties (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (i : ℕ) : Prop :=
  ∃ dg : D.what₂.Tau → ℕ,
    (∀ c c', GL3Theta.IsKer D (tor0 D cc δ) e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')) ∧ GL3Columns.liftTieH D O i dg ∧
    RhoAlg C i ∧ SrcTie M O i dg ∧ TgtTie M O (i + 1) ∧ KFi M i

def StatementJetEntriesAlgebraic (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (i : ℕ) : Prop :=
  Crv D cc δ → t0Ex D → useAlg D → natTie D cc δ e → i < D.R.m → Ties M O cc δ e i → EntIn M i (Qbar : Set ℂ)

end Alg


theorem exists_map_eq {σ : Type} (F : IntermediateField ℚ ℂ) (Q : MvPolynomial σ ℂ) (h : ∀ α, MvPolynomial.coeff α Q ∈ F) :
    ∃ Q₀ : MvPolynomial σ F, MvPolynomial.map (algebraMap F ℂ) Q₀ = Q := by
  refine ⟨∑ α ∈ Q.support, MvPolynomial.monomial α (⟨MvPolynomial.coeff α Q, h α⟩ : F), ?_⟩
  conv_rhs => rw [Q.as_sum]
  simp only [map_sum, MvPolynomial.map_monomial]
  rfl

theorem coeff_map_mem {σ : Type} (F : IntermediateField ℚ ℂ) (Q₀ : MvPolynomial σ F) (α : σ →₀ ℕ) :
    MvPolynomial.coeff α (MvPolynomial.map (algebraMap F ℂ) Q₀) ∈ F := by
  rw [MvPolynomial.coeff_map]
  exact (MvPolynomial.coeff α Q₀).2

def evF (D : D7) (F : IntermediateField ℚ ℂ) {N : ℕ} (f : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) :
    MvPolynomial (GL3Theta.FrV D N) F →+* ℂ :=
  MvPolynomial.eval₂Hom (algebraMap F ℂ) (fun k : GL3Theta.FrV D N => f k.1 k.2.1 k.2.2)

theorem evFr_map (D : D7) (F : IntermediateField ℚ ℂ) {N : ℕ} (f : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ)
    (R : MvPolynomial (GL3Theta.FrV D N) F) : GL3Theta.evFr D (MvPolynomial.map (algebraMap F ℂ) R) f = evF D F f R := by
  simp only [GL3Theta.evFr, evF, MvPolynomial.eval_map, MvPolynomial.coe_eval₂Hom]

def polG (D : D7) (F : IntermediateField ℚ ℂ) {N N' : ℕ} (s : D.what₂.Tau → F) :
    MvPolynomial (GL3Theta.FrV D N) F →+* MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') F) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
    MvPolynomial.C (MvPolynomial.C (s k.1) * (if h : (k.2.2 : ℕ) < N' then MvPolynomial.X ((k.1, b, ⟨k.2.2, h⟩) : GL3Theta.FrV D N') else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : GL3Theta.Idx D N N'))

theorem polD_eq (D : D7) (F : IntermediateField ℚ ℂ) {N N' : ℕ} (s : D.what₂.Tau → F) (Q₀ : MvPolynomial (GL3Theta.FrV D N) F)
    (f : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    GL3Theta.polD D (fun τ => (s τ : ℂ)) (MvPolynomial.map (algebraMap F ℂ) Q₀) f = MvPolynomial.map (evF D F f) (polG D F s Q₀) := by
  unfold GL3Theta.polD
  induction Q₀ using MvPolynomial.induction_on
  next a =>
    simp [polG, evF]
  next p q hp hq =>
    simp only [map_add, hp, hq]
  next p n hp =>
    simp only [map_mul] at hp ⊢
    rw [hp]
    refine congrArg₂ (· * ·) rfl ?_
    by_cases hn : (n.2.2 : ℕ) < N'
    · simp [polG, evF, hn]
    · simp [polG, evF, hn]


def detP (D : D7) (F : IntermediateField ℚ ℂ) (N : ℕ) (τ : D.what₂.Tau) : MvPolynomial (GL3Theta.FrV D N) F :=
  Matrix.det (Matrix.of fun a b : Fin N => (MvPolynomial.X ((τ, a, b) : GL3Theta.FrV D N) : MvPolynomial (GL3Theta.FrV D N) F))






def entAlgAll (D : D7) (Tw : TwForms D) : Prop :=
  (∀ u, ∀ i < D.R.m, EntIn (D.fm u) i (Qbar : Set ℂ)) ∧ ∀ u w, ∀ i < D.R.m, EntIn (Tw.fm u (D.what₂.muAt w)) i (Qbar : Set ℂ)

theorem exists_field (D : D7) (S : Set ℂ) (hS : S.Finite) (hA : S ⊆ (Qbar : Set ℂ)) :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ Set.range D.what₂.embLL ⊆ (F : Set ℂ) ∧ S ⊆ (F : Set ℂ) := by
  classical
  haveI := D.nfLL
  haveI : Finite S := hS.to_subtype
  haveI h1 : FiniteDimensional ℚ D.what₂.embLL.toRatAlgHom.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom).toLinearEquiv
  haveI h2 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => mem_algebraicClosure_iff'.mp (hA hx)
  refine ⟨D.what₂.embLL.toRatAlgHom.fieldRange ⊔ IntermediateField.adjoin ℚ S, inferInstance, ?_, ?_⟩
  · rintro z ⟨y, rfl⟩
    exact (le_sup_left : D.what₂.embLL.toRatAlgHom.fieldRange ≤ _) (AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩)
  · intro z hz
    exact (le_sup_right : IntermediateField.adjoin ℚ S ≤ _) (IntermediateField.subset_adjoin ℚ S hz)

def muFin (D : D7) : Prop := (Set.range D.what₂.muAt).Finite



def TiesMem (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ u, ∃ O : GL3Theta.LiftObj D (D.mem u).C, O.IsMem ∧ ∀ i < D.R.m, Ties (D.fm u) O cc δ e i

def TiesTw (D : D7) (Tw : TwForms D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ u w, ∃ O : GL3Theta.LiftObj D (D.chTw u (D.what₂.muAt w)), ∀ i < D.R.m, Ties (Tw.fm u (D.what₂.muAt w)) O cc δ e i



def kRatTwF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Tw : ∀ x (i : Fm.Ix x), TwForms (Fm.D x i)) : Prop :=
  ∀ x (i : Fm.Ix x), kRatTw (Fm.D x i) (Tw x i)

def LLKerF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Tw : ∀ x (i : Fm.Ix x), TwForms (Fm.D x i)) : Prop :=
  ∀ x (i : Fm.Ix x), LLKer (Fm.D x i) (Tw x i)


end Formalism.MainNotions.AlgebraicJets
