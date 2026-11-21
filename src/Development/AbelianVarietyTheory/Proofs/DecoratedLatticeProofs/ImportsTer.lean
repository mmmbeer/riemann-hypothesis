import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.UnitPairEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.SymmetricPatternGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombination

section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Plain
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}

abbrev sE {n m : Type*} (e : n ≃ m) (c : ℕ) : n ⊕ Fin c ≃ m ⊕ Fin c := e.sumCongr (Equiv.refl _)





theorem mul_embX_mem_R {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (g : GL n k) :
    u * embX c g ∈ R k n c p :=
  mul_mem ((le_sup_right : N k n c p ≤ R k n c p) hu) ((le_sup_left : (embX c).range ≤ R k n c p) ⟨g, rfl⟩)





end Plain

section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}


omit [DecidableEq n] [DecidableEq m] [DecidableEq n'] [DecidableEq m'] in
theorem opE_submatrix [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
    (p : ℕ) (e : n ≃ m) (e' : n' ≃ m') (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix m m' k) :
    opE ψ ν p (fun x => Φ (x.submatrix (sE e c) (sE e' (c + 1)))) x₀ = opE ψ ν p Φ (x₀.submatrix e e') := by
  classical
  have := secondCountable k
  have := t2Space k
  have hf : ∀ r s, Free p (r, s) ↔ Free p (sE e c r, sE e' (c + 1) s) := by
    rintro (r | r) (s | s) <;> exact Iff.rfl
  let σ : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} ≃ {rs : (m ⊕ Fin c) × (m' ⊕ Fin (c + 1)) // Free p rs} :=
    ((sE e c).prodCongr (sE e' (c + 1))).subtypeEquiv fun rs => hf rs.1 rs.2
  have h1 : ∀ f, (affPt p x₀ f).submatrix (sE e c) (sE e' (c + 1)) =
      affPt p (x₀.submatrix e e') (MeasurableEquiv.piCongrLeft (fun _ => k) σ.symm f) := fun f => by
    have h2 : ∀ a, MeasurableEquiv.piCongrLeft (fun _ => k) σ.symm f a = f (σ a) := fun a => by
      obtain ⟨a, rfl⟩ := σ.symm.surjective a
      rw [MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
    ext r s
    have hb : basePt c x₀ (sE e c r) (sE e' (c + 1) s) = basePt c (x₀.submatrix e e') r s := by
      rcases r with r | r <;> rcases s with s | s <;> rfl
    simp only [affPt, submatrix_apply, Matrix.add_apply, hb, of_apply, h2]
    by_cases h : Free p (r, s)
    · rw [dif_pos h, dif_pos ((hf r s).1 h)]; rfl
    · rw [dif_neg h, dif_neg fun H => h ((hf r s).2 H)]
  unfold opE
  rw [← (measurePreserving_piCongrLeft (fun _ => ν) σ.symm).integral_comp']
  simp only [← h1]
  rfl



theorem reGL_symm_mem_KO (e : n ≃ m) {g : GL m k} : (reGL e).symm g ∈ KO k n ↔ g ∈ KO k m :=
  ⟨fun h => ((TypeDatum.full k n).reindex e).le_KO h, fun h => ((TypeDatum.full k m).reindex e.symm).le_KO
    (show (reGL e.symm).symm ((reGL e).symm g) ∈ KO k m by
      have : (reGL e.symm).symm ((reGL e).symm g) = g := by ext i j; simp [reGL_symm_val]
      rwa [this])⟩

theorem exists_reindex_iff (P : TypeDatum k n) (e : n ≃ m) (M : Matrix m m k) :
    (∃ g ∈ (P.reindex e).J, g.val = M) ↔ ∃ g ∈ P.J, g.val = M.submatrix e e := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, hg, rfl⟩
  · rintro ⟨g, hg, h⟩
    refine ⟨reGL e g, ?_, by rw [reGL_val, h]; simp⟩
    change (reGL e).symm (reGL e g) ∈ P.J
    rwa [MulEquiv.symm_apply_apply]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] in
theorem maxM_submatrix (e : n ≃ m) (e' : n' ≃ m') (M : Matrix m m' k) : MaxM (M.submatrix e e') ↔ MaxM M :=
  ⟨fun h i j => by simpa using h (e.symm i) (e'.symm j), fun h _ _ => h _ _⟩

theorem det_reGL_symm (e : n ≃ m) (g : GL m k) :
    Matrix.GeneralLinearGroup.det ((reGL e).symm g) = Matrix.GeneralLinearGroup.det g := by
  rw [← det_reGL e, MulEquiv.apply_symm_apply]


omit [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] in
theorem Phi_reindex (P : TypeDatum k n) (e : n ≃ m) (f : n' ≃ m') (μ : kˣ →* ℂˣ) (x : Matrix (m ⊕ m') m k) :
    (P.reindex e).Phi m' μ x = P.Phi n' μ (x.submatrix (e.sumCongr f) e) := by
  have hi : (P.reindex e).Phi m' μ x ≠ 0 ↔ P.Phi n' μ (x.submatrix (e.sumCongr f) e) ≠ 0 := by
    rw [TypeDatum.Phi_ne_zero_iff, TypeDatum.Phi_ne_zero_iff, exists_reindex_iff, ← maxM_submatrix f e]
    rfl
  by_cases h : (P.reindex e).Phi m' μ x = 0
  · rw [h, not_not.1 (hi.not.1 (not_not.2 h))]
  · obtain ⟨⟨g, hg, eg⟩, h2⟩ := (TypeDatum.Phi_ne_zero_iff _ _).1 h
    rw [TypeDatum.Phi_of_mem _ μ ⟨g, hg⟩ eg h2, TypeDatum.Phi_of_mem _ μ (x := x.submatrix (e.sumCongr f) e) ⟨(reGL e).symm g, hg⟩
      (by rw [reGL_symm_val, eg]; rfl) ((maxM_submatrix f e _).2 h2), det_reGL_symm]
    rfl

end Local

section Iter
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t t' : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype t'] [DecidableEq t']

abbrev eI (r : Type*) {t t' : Type*} (f : t ≃ t') (j : ℕ) : Ix r t j ≃ Ix r t' j :=
  (Equiv.refl r).sumCongr ((Equiv.refl (Fin j)).prodCongr f)





variable {κ : Type*} [Fintype κ] [DecidableEq κ] {s : ℕ}



end Iter

end GlobalTheory.SymCompare
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open GlobalTheory.FinPl (SplitPt grpAt grpOff)
open GlobalTheory.SymCompare (sE)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.CompactOpenVolumes (places IsUnitPair put biPut volK IsCptOpen RowComb)

namespace GlobalTheory.QCmp

section Many
variable {D : D7} {I : Type} [Fintype I] [DecidableEq I] {k : I → Type} [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
  [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
variable {Y Y' : I → Type} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] [∀ i, Fintype (Y' i)] [∀ i, DecidableEq (Y' i)]

def Emb (q : ∀ i, SplitPt D (k i)) (V : HSp D) (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i))
    (ι : (∀ i, GL (Y i) (k i)) → GA D V) : Prop :=
  ∀ x, ι x ∈ grpAt V (places q) ∧ ∀ i, (mt V (ι x)).map (q i).pr = (F i).β * (x i).val * (F i).γ

end Many

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def Same (Q Q' : QStep S) : Prop :=
  Q'.q.v = Q.q.v ∧ (∀ x, IntAt Q'.q.v Q'.gl₁ x ↔ IntAt Q.q.v Q.gl₁ x) ∧ (∀ x, IntAt Q'.q.v Q'.gl₂ x ↔ IntAt Q.q.v Q.gl₂ x) ∧
    Q'.D₁ = Q.D₁ ∧ Q'.D₂ = Q.D₂ ∧ Q'.e₀.mapDomain Q'.gl₀ = Q.e₀.mapDomain Q.gl₀ ∧ Q'.volJ = Q.volJ ∧
    (∀ f₁ f₂, Q.Vac f₁ f₂ → Q'.Vac f₁ f₂) ∧ (∀ f, Q.Typed f → Q'.Typed f) ∧
    ∃ (a : Q.A₁ ≃ Q'.A₁) (b : Q.A₂ ≃ Q'.A₂), (∀ γ, Q'.w₁ (a γ) = Q.w₁ γ ∧ Q'.d₁ (a γ) = Q.d₁ γ) ∧
      (∀ β, Q'.w₂ (b β) = Q.w₂ β ∧ (Q'.e₂ (b β)).mapDomain Q'.gl₂ = (Q.e₂ β).mapDomain Q.gl₂) ∧
      ∀ γ β, Q'.d₂ (a γ) (b β) = Q.d₂ γ β

theorem Same.refl (Q : QStep S) : Same Q Q :=
  ⟨rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, rfl, rfl, rfl, rfl, fun _ _ h => h, fun _ h => h, Equiv.refl _, Equiv.refl _,
    fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩

def reFrame {k : Type} [Field k] {N : ℕ} {Y Z : Type} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (F : GlobalTheory.LocMod.Frame k N Y) (e : Y ≃ Z) : GlobalTheory.LocMod.Frame k N Z where
  β := F.β.submatrix id e.symm
  γ := F.γ.submatrix e.symm id
  βγ := by rw [submatrix_mul_equiv, F.βγ, submatrix_id_id]
  γβ := by
    rw [show F.γ.submatrix e.symm id * F.β.submatrix id e.symm = (F.γ * F.β).submatrix e.symm e.symm from
      submatrix_mul_equiv _ _ _ (Equiv.refl _) _, F.γβ, submatrix_one_equiv]

end GlobalTheory.QCmp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open GlobalTheory.FinPl (SplitPt grpAt grpOff)
open GlobalTheory.SymCompare (sE)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QCmp

noncomputable section

namespace GlobalTheory.CombThetaAny

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (C : WO S T →₀ ℂ)
    (f : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T (comb ψ S T C f) := by
  intro D ψ hψ S T C f hf
  have e : comb ψ S T C f = fun u => ∑ x ∈ C.support, C x * (ψ (symplOH S T u x) * f (u + x)) := by
    funext u; exact GlobalTheory.FrComb.comb_apply C f u
  refine ⟨fun γ u => ?_, ?_, ?_, ?_⟩
  · simp only [GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [add_assoc, hf.quasi, GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right]
    have key : ψ (symplOH S T (ratW T S γ) x + symplOH S T u x) * ψ (-(symplOH S T (ratW T S γ) u + symplOH S T (ratW T S γ) x)) =
        ψ (-(symplOH S T (ratW T S γ) u)) * ψ (symplOH S T u x) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; congr 1; ring
    linear_combination (C x * f (u + x)) * key
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVf⟩ := GlobalTheory.FrCombAny.exists_orth_any hψ C.support
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' => ?_⟩
    exact GlobalTheory.FrComb.heisO_comb (hVf a ha.2 ha') (hUf a ha.1 ha')
  · rw [e]
    exact continuous_finset_sum _ fun x _ => continuous_const.mul
      ((hψ.1.1.comp (GlobalTheory.FinTranslate.continuous_symplOH S T x)).mul
        (hf.cont.comp (continuous_id.add continuous_const)))
  · intro n L hL hLf w
    rw [e]
    have e2 : (fun t => ∑ x ∈ C.support, C x * (ψ (symplOH S T (w + L t) x) * f (w + L t + x))) =
        fun t => ∑ x ∈ C.support, C x * (ψ (symplOH S T w x) * (ψ (symplOH S T (L t) x) * f (w + x + L t))) := by
      funext t
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [GlobalTheory.FinTranslate.symplOH_add_left, AddChar.map_add_eq_mul, add_right_comm, mul_assoc]
    simp only []
    rw [e2]
    exact ContDiff.sum fun x _ => contDiff_const.mul (contDiff_const.mul
      ((GlobalTheory.FrCombAny.contDiff_psi hψ hL hLf x).mul (hf.smooth n L hL hLf (w + x))))

end GlobalTheory.CombThetaAny

end
end
