import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValConjSubLt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasResOfValSubLt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletion

section
noncomputable section

namespace GlobalTheory.SeeSaw.LevMem

section Columns

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.LevRead GlobalTheory.Mem.Col2.TC.GLev0 Matrix
open scoped TensorProduct

section Pts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsInt (m : GL (Fin n) (AfE F E)) : Prop := (∀ i j, m.1 i j ∈ RInt F E) ∧ ∀ i j, (m⁻¹).1 i j ∈ RInt F E

theorem isInt_of {m : GL (Fin n) (AfE F E)} (h : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔ ∀ i, (m.1 *ᵥ z) i ∈ RInt F E) :
    IsInt m := by
  have h1 : ∀ j i, (Pi.single j 1 : Fin n → AfE F E) i ∈ RInt F E := fun j i => by
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨fun i j => by simpa using (h _).1 (h1 j) i, fun i j => ?_⟩
  have := (h ((m⁻¹).1 *ᵥ Pi.single j 1)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact h1 j) i
  simpa using this

variable [StarRing E] {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

end Pts

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

end Columns

section LocalField

open ValuativeRel IsLocalRing Matrix GlobalTheory.LatPair
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos Reduces)

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

end LocalField

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge

section Adelic

variable {D : D7}

theorem mem_latHat_iff {n : ℕ} {L : Set (Fin n → D.host.E)} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D n)
    (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) : z ∈ latHat D.host.F D.host.E L ↔ ∀ i, z i ∈ intAE D := by
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a, ha, ⟨x i, (hL x).1 hx i⟩, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro h
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := h i
    generalize z i = c at hi
    induction hi using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), (hL _).2 fun j => ?_, funext fun j => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [x.isIntegral_coe, isIntegral_zero]
      · rw [Pi.single_apply, Pi.single_apply]
        split_ifs
        exacts [rfl, (TensorProduct.tmul_zero _ _).symm]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

set_option maxHeartbeats 1000000 in

theorem moves_iff {V : HSp D} {L : GlobalTheory.FinPl.Lat V} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D V.rank) {κ : GA D V} {n : ℕ} (hn : V.rank = n)
    {y : GL (Fin n) (EF D)} (hy : finM V hn κ = y.1) :
    GlobalTheory.FinPl.Moves V κ L L (fun _ => True) ↔ IsInt (F := D.host.F) (E := D.host.E) y := by
  subst hn
  have h1 : ∀ a : Fin V.rank → AE D, (∀ i, a i ∈ GlobalTheory.FinPl.idAt D fun _ => True) →
      (a ∈ GlobalTheory.FinPl.latV V L (fun _ => True) ↔ ∀ i, toEAf D (a i) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E) := fun a ha =>
    (GlobalTheory.FinPl.KOpen.mem_latV_iff V L _ a ha).trans ((mem_latHat_iff hL _).trans
      (forall_congr' fun i => GlobalTheory.IdemSupport.mem_intAE_iff _))
  have h2 : ∀ (a : Fin V.rank → AE D) i, toEAf D ((mt V κ *ᵥ a) i) = (y.1 *ᵥ fun j => toEAf D (a j)) i := fun a i => by
    rw [← hy]
    exact RingHom.map_mulVec (toEAf D) _ a i
  constructor
  · intro h
    refine isInt_of fun z => ?_
    let sw := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
    choose a ha ha' using fun i => GlobalTheory.KStabBridge.exists_fin_lift (D := D) (sw.symm (z i))
    have hz : ∀ i, toEAf D (a i) = z i := fun i => (congrArg sw (ha' i)).trans (sw.apply_symm_apply _)
    have hi : ∀ i, a i ∈ GlobalTheory.FinPl.idAt D fun _ => True := fun i =>
      Submodule.mem_inf.2 ⟨ha i, (Submodule.mem_iInf _).2 fun u => absurd trivial u.2⟩
    have := h a hi
    rw [h1 a hi, h1 _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ κ hi)] at this
    simp only [h2, hz] at this
    exact this
  · intro h a ha
    rw [h1 a ha, h1 _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ κ ha)]
    simp only [h2]
    refine ⟨PtExist.mulVec_int h.1, fun h' i => ?_⟩
    have := PtExist.mulVec_int h.2 h' i
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

section Split

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E}

end Split

variable {u : D.what₂.Word} {a : XPart D u}

end Adelic

end GlobalTheory.SeeSaw.LevMem

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FinPl.AwayLevel.single_natCast_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (T : ℕ) (j b : Fin n) [Decidable (b = j)] :
    (Pi.single j (T : K) : Fin n → K) b = ((if b = j then (T : 𝓞 K) else 0 : 𝓞 K) : K) := by
  by_cases hb : b = j
  · subst hb
    simp
  · simp [hb]

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.FinPl.AwayLevel.mem_levelVL_base : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.True → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => True) → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ Formalism.UG.levelVL (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) v (F0 W u).cls0.lev.Lb := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a hat κ hκ y hy hmv v hv
  have hL := (hat.pinX.xs 0 (Nat.zero_le _)).2.2
  have hint := (GlobalTheory.SeeSaw.LevMem.moves_iff hL _ hy).1 hmv
  obtain ⟨k, hR⟩ := (hA.tr.std.some u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hLb : ∀ x, x ∈ (F0 W u).cls0.lev.Lb ↔ x ∈ TC.baseL B (B.R.N 0) (X.piT u) := hR.lb ()
  have hv' : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal := hv
  have h1 : ∀ x ∈ (F0 W u).cls0.lev.Lb, ∀ j, ∃ r : 𝓞 (I.rec7 l Z).host.E, x j = r := fun x hx j => by
    obtain ⟨r, hr, -⟩ := (hLb x).1 hx j
    exact ⟨r, hr⟩
  have h2 : ∀ j, (Pi.single j ((B.T u : ℕ) : (I.rec7 l Z).host.E) : Fin ((I.rec7 l Z).R.N 0) → (I.rec7 l Z).host.E) ∈ (F0 W u).cls0.lev.Lb := fun j =>
    (hLb _).2 fun b => by
      have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
      refine ⟨if b = j then (B.T u : 𝓞 B.host.E) else 0, ?_, fun _ => ?_⟩
      · exact GlobalTheory.FinPl.AwayLevel.single_natCast_eq (K := B.host.E) (B.T u) j b
      · split_ifs
        · refine ⟨B.fields.conjO ((B.primes X).piT u), ?_⟩
          rw [hPr.piT_norm u]
        · exact dvd_zero _
  have hS := fun x => GlobalTheory.Mem.Col2.LevRead.mem_latS_iff hv' h1 h2 x
  have hmul : ∀ (N : GL (Fin ((I.rec7 l Z).R.N 0)) (Formalism.L2.DIV.AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), (∀ i j, N.1 i j ∈ Formalism.L2.DIV.RInt (I.rec7 l Z).host.F (I.rec7 l Z).host.E) →
      ∀ x : Fin ((I.rec7 l Z).R.N 0) → (I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F, (∀ b, x b ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v) →
        ∀ b, ((Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) N).1 *ᵥ x) b ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E v := fun N hN x hx b => by
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (Formalism.UG.P.afsplit_prV_int v _ (hN b j)) (hx j)
  refine Subgroup.mem_inf.2 ⟨GlobalTheory.MemDual.bc_prV_mem_UPts _ _ v y.2, fun x => ?_⟩
  rw [hS, hS]
  refine ⟨hmul _ hint.1 x, fun h b => ?_⟩
  have := hmul _ hint.2 _ h b
  rwa [map_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
end
