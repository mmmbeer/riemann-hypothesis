import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorConditionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EmbZeroTrivialWittDecomposition

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LJPos

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

def IsIntM {ι κ : Type} (x : Matrix ι κ (Fv F v)) : Prop := ∀ i j, x i j ∈ v.adicCompletionIntegers F

variable (F v) in

def KL (n : ℕ) : Subgroup (GL (Fin (n + n)) (Fv F v)) where
  carrier := {g | IsIntM g.1 ∧ IsIntM (g⁻¹).1}
  mul_mem' := by
    intro a b ha hb
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simp only [Units.val_mul, Matrix.mul_apply]
      exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ha.1 i k) (hb.1 k j)
    · simp only [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hb.2 i k) (ha.2 k j)
  one_mem' := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
    · simp only [inv_one, Units.val_one, Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
  inv_mem' := by
    intro a ha
    exact ⟨ha.2, by simpa using ha.1⟩

def nM {n : ℕ} (x : Matrix (Fin n) (Fin n) (Fv F v)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v) := blk4 1 x 0 1

def nL {n : ℕ} (x : Matrix (Fin n) (Fin n) (Fv F v)) : GL (Fin (n + n)) (Fv F v) where
  val := nM x
  inv := nM (-x)
  val_inv := by
    simp only [nM, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  inv_val := by
    simp only [nM, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]

def botMinor {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v)) (e : Fin n → Fin (n + n)) :
    Matrix (Fin n) (Fin n) (Fv F v) :=
  Matrix.of fun i j => g (Fin.natAdd n i) (e j)

def hB {n : ℕ} (g : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v)) : ℝ≥0 :=
  Finset.univ.sup' ⟨fun i => Fin.natAdd n i, Finset.mem_univ _⟩ fun e : Fin n → Fin (n + n) => ‖(botMinor g e).det‖₊

instance instMeasGL (n : ℕ) : MeasurableSpace (GL (Fin (n + n)) (Fv F v)) := borel _
instance instBorelGL (n : ℕ) : BorelSpace (GL (Fin (n + n)) (Fv F v)) := ⟨rfl⟩

end PositivityTheory.Rg.Rsw.L.LJPos

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LJPos

structure SplitPkg (D : D7) (v : Pl D) where
  π : Fv D.host.F v ⊗[D.host.F] D.host.E ≃ₐ[Fv D.host.F v] Fv D.host.F v × Fv D.host.F v
  swap : ∀ y, π (sigR (Fv D.host.F v) D.sp.cm.sig y) = (π y).swap
  int : ∀ y, y ∈ intLoc D.host.F D.host.E v ↔
    (π y).1 ∈ v.adicCompletionIntegers D.host.F ∧ (π y).2 ∈ v.adicCompletionIntegers D.host.F

def PlaceEx : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ →
  ∀ r : ℕ, ResEta D χ r → ∀ S : Finset (Pl D), ∃ v ∉ S, ∃ P : SplitPkg D v,
    (∀ a : Fv D.host.F v, (∀ b ∈ v.adicCompletionIntegers D.host.F, psiV D.host.F ψ v (a * b) = 1) ↔
      a ∈ v.adicCompletionIntegers D.host.F) ∧
    (∀ u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (P.π u).1 ∈ v.adicCompletionIntegers D.host.F →
      (P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1 ∈ v.adicCompletionIntegers D.host.F → (P.π u).2 = 1 →
      χ (ideleAt D.host.F D.host.E v u) = 1) ∧
    ∀ u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (P.π u).1 = (P.π u).2 → χ (ideleAt D.host.F D.host.E v u) = 1

end PositivityTheory.Rg.Rsw.L.LJPos

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LJPos

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU tensNU_tmul)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

def pkgOf (D : D7) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : SplitPkg D v where
  π := splitAlgEquiv (isCMExt_host D) τ
  swap := splitAlgEquiv_sigR (isCMExt_host D) τ
  int := fun _ => mem_intLoc_iff_split (isCMExt_host D) τ

theorem sigR_tensNU {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (σ : E →ₐ[F] E) (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (y : R ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R' σ (tensNU j hj y) = tensNU j hj (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem conjUnit_ideleAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (w : (Fv F v ⊗[F] E)ˣ) :
    conjUnit σ (ideleAt F E v w) = ideleAt F E v (conjUnit σ w) := by
  refine Units.ext ?_
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (1 - tensNU (inFin v) (inFin_mul v) 1 + tensNU (inFin v) (inFin_mul v) w.1) =
    1 - tensNU (inFin v) (inFin_mul v) 1 + tensNU (inFin v) (inFin_mul v) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ w.1)
  rw [map_add, map_sub, map_one, sigR_tensNU, sigR_tensNU, map_one]

theorem resEta_norm {D : D7} {χ : (AE D)ˣ →* Circle} {r : ℕ} (h : ResEta D χ r) (x : (AE D)ˣ) :
    χ (x * conjUnit D.sp.cm.sig x) = 1 := by
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  have e : x * conjUnit D.sp.cm.sig x =
      idF D (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) x) :=
    Units.ext (algebraMap_norm_eq (isCMExt_host D) x.1).symm
  rw [e, h2 η hη, hη.2.2.1, one_pow]

theorem diag_eq_norm {D : D7} {v : Pl D} (P : SplitPkg D v) (u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)
    (hu : (P.π u).1 = (P.π u).2) : ∃ w, u = w * conjUnit D.sp.cm.sig w := by
  have h1 : (P.π u).1 * (P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1 = 1 := by
    rw [← Prod.fst_mul, ← map_mul, Units.mul_inv, map_one, Prod.fst_one]
  refine ⟨⟨P.π.symm ((P.π u).1, 1), P.π.symm ((P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1, 1), ?_, ?_⟩,
    Units.ext (P.π.injective ?_)⟩
  · rw [← map_mul, Prod.mk_mul_mk, h1, mul_one]; exact map_one _
  · rw [← map_mul, Prod.mk_mul_mk, mul_comm, h1, mul_one]; exact map_one _
  · change _ = P.π (P.π.symm ((P.π u).1, 1) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig (P.π.symm ((P.π u).1, 1)))
    rw [map_mul, P.swap, AlgEquiv.apply_symm_apply]
    exact Prod.ext (by simp) (by simp [hu])

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : HeightOneSpectrum (𝓞 F)}

omit [NumberField E] in
theorem snd_tensNU_mem {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensNU (inFin v) (inFin_mul v) y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  refine intLoc_induction (p := fun y => Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
      (tensNU (inFin v) (inFin_mul v) y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)})
    (fun a ha x => AddSubgroup.subset_closure ⟨singleFin v a, fun w => ?_, x, rfl⟩) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · by_cases hw : w = v
    · subst hw; rw [evalV_singleFin_self]; exact ha
    · rw [evalV_singleFin_ne hw]; exact zero_mem _
  · rw [map_zero, map_zero]; exact zero_mem _
  · rw [map_add, map_add]; exact add_mem hy hz
  · rw [map_neg, map_neg]; exact neg_mem hy

omit [NumberField E] in
theorem snd_ideleAt_mem {u : (Fv F v ⊗[F] E)ˣ} (hu : u.1 ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (ideleAt F E v u).1 ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  rw [ideleAt, val_extUnit, map_add, map_sub, map_one]
  exact add_mem (sub_mem (AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, 1, rfl⟩)
    (snd_tensNU_mem (one_mem _))) (snd_tensNU_mem hu)

omit [NumberField E] in
theorem eval_snd_ideleAt {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (u : (Fv F v ⊗[F] E)ˣ) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (ideleAt F E v u).1) = 1 := by
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
  exact map_extUnit_zero _ (inFin v) (inFin_mul v) (fun a => evalV_singleFin_ne hw a) u

omit [NumberField E] in
theorem fst_ideleAt (u : (Fv F v ⊗[F] E)ˣ) :
    Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (ideleAt F E v u).1 = 1 :=
  map_extUnit_zero _ _ _ (fun _ => rfl) u

end Gen

theorem unram_ideleAt {D : D7} {χ : (AE D)ˣ →* Circle} {v : Pl D} (h : CharUnramAt D χ v)
    {u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ} (hu : u.1 ∈ intLoc D.host.F D.host.E v)
    (hu' : (u⁻¹).1 ∈ intLoc D.host.F D.host.E v) : χ (ideleAt D.host.F D.host.E v u) = 1 := by
  refine h _ (fst_ideleAt u) (fun w hw => eval_snd_ideleAt hw u) (snd_ideleAt_mem hu) ?_
  rw [← MonoidHom.map_inv]
  exact snd_ideleAt_mem hu'

theorem placeEx : PlaceEx := by
  classical
  intro D ψ hψ χ hχ r hr S
  have hev := (GlobalTheory.T.character_conductor_condition D.host.F ψ hψ).and (GlobalTheory.FinPl.LastInhab.eventually_charUnramAt D χ hχ.1)
  obtain ⟨v, hv, ⟨τ⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem (isCMExt_host D) (S ∪ (Filter.eventually_cofinite.1 hev).toFinset)
  rw [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  refine ⟨v, hv.1, pkgOf D v τ, hv.2.1, fun u h1 h2 h3 => ?_, fun u hu => ?_⟩
  · refine unram_ideleAt hv.2.2 (((pkgOf D v τ).int _).2 ⟨h1, by rw [h3]; exact one_mem _⟩)
      (((pkgOf D v τ).int _).2 ⟨h2, ?_⟩)
    have e : ((pkgOf D v τ).π u).2 * ((pkgOf D v τ).π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).2 = 1 := by
      rw [← Prod.snd_mul, ← map_mul, Units.mul_inv, map_one, Prod.snd_one]
    rw [h3, one_mul] at e
    rw [e]; exact one_mem _
  · obtain ⟨w, rfl⟩ := diag_eq_norm _ u hu
    rw [map_mul, ← conjUnit_ideleAt]
    exact resEta_norm hr _

end PositivityTheory.Rg.Rsw.L.LJPos

end
end
