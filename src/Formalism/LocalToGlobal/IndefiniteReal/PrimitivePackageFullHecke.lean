import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
import Formalism.LocalToGlobal.IndefiniteReal.InBlock
import Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
import Formalism.LocalToGlobal.GlobalTheory.PassageBaseSymmetricLevels
import Formalism.LocalToGlobal.IndefiniteReal.MajorantAtBaseEqInnerOfPackage
import Formalism.LocalToGlobal.IndefiniteReal.RowGSurj
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfMemRangeAdjoint
import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsBaseLevel

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

section Bridge

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {U : Type} [AddCommGroup U] [Module K U]

theorem epOp_eq_epP (σ : Representation K G U) (P : Subgroup G) (ψ : P →* Kˣ) (χ : P →* (𝓞 K)ˣ)
    (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    Formalism.IndefR.IndefiniteEpsilonOperator.epOp σ ⟨P, ψ⟩ = Formalism.IndefR.TransferLatticeStatement.epP P χ σ := by
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.epOp Formalism.IndefR.TransferLatticeStatement.epP
  simp only [hχ]
  congr
  exact Subsingleton.elim _ _

theorem nOf_eq_nS {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W) (P : Subgroup G) (ψ : P →* Kˣ)
    (χ : P →* (𝓞 K)ˣ) (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨P, ψ⟩ = Formalism.IndefR.TransferLatticeStatement.nS τ P χ := by
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.TransferLatticeStatement.nS
  first
  | (unfold Formalism.IndefR.IndefiniteEpsilonOperator.epSp; rw [epOp_eq_epP τ P ψ χ hχ])
  | (simp only [Formalism.IndefR.IndefiniteEpsilonOperator.epSp, epOp_eq_epP τ P ψ χ hχ])
  | (rw [← epOp_eq_epP τ P ψ χ hχ]; rfl)

end Bridge

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

def rep (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) : Representation K G (Fin I.Sg.D → K) where
  toFun g := Matrix.toLin' (I.ρf g)
  map_one' := by rw [h1, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [hm, Matrix.toLin'_mul]; rfl

theorem rep_apply (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) (g : G) (x : Fin I.Sg.D → K) :
    I.rep h1 hm g x = I.ρf g *ᵥ x := by
  first
  | rfl
  | simp [rep, Matrix.toLin'_apply]

theorem epM_eq (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) (P : Subgroup G) (ψ : P →* Kˣ)
    (χ : P →* (𝓞 K)ˣ) (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    (I.epM P ψ).mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP P χ (I.rep h1 hm) := by
  classical
  rw [← epOp_eq_epP (I.rep h1 hm) P ψ χ hχ]
  apply LinearMap.ext
  intro x
  unfold epM Formalism.IndefR.IndefiniteEpsilonOperator.epOp
  rw [Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.sum_mulVec, LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Matrix.smul_mulVec, LinearMap.smul_apply, rep_apply, map_inv]

theorem eMat_eq (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) {W : Type} [AddCommGroup W]
    [Module K W] (τ : Representation K G W) :
    (I.eMat τ).mulVecLin = Formalism.IndefR.TransferLatticeStatement.eS τ (I.rep h1 hm) := by
  apply LinearMap.ext
  intro x
  unfold eMat Formalism.IndefR.TransferLatticeStatement.eS
  rw [Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.sum_mulVec, LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.smul_mulVec, LinearMap.smul_apply, rep_apply]

theorem passage_of_steps [IsTotallyComplex K] {s : ℕ} (H : I.Hyp s) {S : Type} [Fintype S] {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) (N : IndefNum I.A.fam.base)
    (hρ : I.PRho) (hJ : I.PJ) (hR : I.PRange) (hMet : I.PMet) (hFr : I.PFrames) (hU : I.PUni)
    (hLat : I.PLat) (hGL : I.PGLat) (hS : I.PSand) (hGood : I.PGood τ)
    (hτ : Formalism.IndefR.TransferLatticeStatement.IsGood τ) (hX : CharsX τ I.A.fam.X) (hM1 : Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨I.P0, I.ψ0⟩) (hn : 0 < nbar)
    (hM2 : NearConstantMultiplicities τ ⟨I.P1, I.ψ1⟩ nbar N.de) (hla : N.la = Formalism.IndefR.IndefiniteEpsilonOperator.la G) :
    Passage N (I.Sb false) (I.Sb true) := by
  obtain ⟨h1, hm, -⟩ := hρ s H
  obtain ⟨χ0, hχ0⟩ := Formalism.IndefR.LatticeTransfer.liftChar K I.P0 I.ψ0
  obtain ⟨χ1, hχ1⟩ := Formalism.IndefR.LatticeTransfer.liftChar K I.P1 I.ψ1
  have hFrm : (I.LA τ nbar).FramesG := hFr s H
  have hL : (I.LA τ nbar).LatG := hLat s H
  have key0 : (I.LA τ nbar).ep0.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P0 χ0 (I.rep h1 hm) :=
    I.epM_eq h1 hm I.P0 I.ψ0 χ0 hχ0
  have key1 : (I.LA τ nbar).ep1.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P1 χ1 (I.rep h1 hm) :=
    I.epM_eq h1 hm I.P1 I.ψ1 χ1 hχ1
  have hs : ∀ t : S, (I.eMat (τ t)).mulVecLin = Formalism.IndefR.TransferLatticeStatement.eS (τ t) (I.rep h1 hm) := fun t =>
    I.eMat_eq h1 hm (τ t)
  have hnS : ∀ t : S, Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ t) ⟨I.P1, I.ψ1⟩ = Formalism.IndefR.TransferLatticeStatement.nS (τ t) I.P1 χ1 := fun t =>
    nOf_eq_nS (τ t) I.P1 I.ψ1 χ1 hχ1
  have hM1' : Formalism.IndefR.TransferLatticeStatement.M1 τ I.P0 χ0 := fun t => by rw [← nOf_eq_nS (τ t) I.P0 I.ψ0 χ0 hχ0]; exact hM1 t
  have hgood : Formalism.IndefR.TransferLatticeStatement.eGood τ (I.rep h1 hm) = LinearMap.id := by
    unfold Formalism.IndefR.TransferLatticeStatement.eGood
    rw [← Finset.sum_congr rfl fun t _ => hs t]
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun M : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K => M *ᵥ x) (hGood s H hτ hX)
    simp only [Matrix.sum_mulVec, Matrix.one_mulVec] at hx
    rw [LinearMap.sum_apply, LinearMap.id_apply]
    simpa only [Matrix.mulVecLin_apply] using hx
  have hst : ∀ g : G, ∀ a ∈ I.Sg.RR, I.rep h1 hm g a ∈ I.Sg.RR := fun g a ha => by
    rw [rep_apply]; exact hGL s H g a ha
  have hUn : Formalism.IndefR.TransferLatticeStatement.IsUnitaryRep (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE (I.rep h1 hm) := fun v g x y => by
    rw [rep_apply, rep_apply]; exact hU s H v g x y
  obtain ⟨hRk, hD0, hD1, hMx⟩ := Formalism.IndefR.LatticeTransfer.levelAmb_transfer (I.LA τ nbar) τ I.P0 χ0 I.P1 χ1 (I.rep h1 hm) hτ hM1'
    key0 key1 hs hnS rfl hgood hFrm hL hst hUn
  have hE : ∀ b, (I.LA τ nbar).EmbAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).XE := fun b =>
    ⟨(hJ s H b).2, hR s H b, hMet s H b⟩
  have hSd : ∀ b, (I.LA τ nbar).SandAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).RR := by
    intro b
    obtain ⟨hin, hout⟩ := hS s H b
    refine ⟨?_, ?_⟩
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨hin x hx, ?_⟩
      show (I.Jm b *ᵥ x) ∈ LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin
      rw [← hR s H b]; exact ⟨x, rfl⟩
    · rintro y ⟨hyR, hyE⟩
      obtain ⟨x, hx, hxy⟩ := hout y hyR hyE
      exact ⟨x, hx, hxy⟩
  have hRows : (I.LA τ nbar).RowsG :=
    ⟨Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm false) _ H.pos0 (hJ s H false).2 (hR s H false),
      Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm true) _ H.pos1 (hJ s H true).2 (hR s H true)⟩
  have hSz : (I.LA τ nbar).Sizes N.la := by
    refine ⟨Nat.card_pos, ?_, Nat.card_pos, ?_, ?_⟩
    · exact (Subgroup.card_le_card_group I.P0).trans (Nat.card_eq_fintype_card).le
    · exact (Subgroup.card_le_card_group I.P1).trans (Nat.card_eq_fintype_card).le
    · rw [hla]; exact le_refl _
  exact passage_from_levels K I.A.fam.base _ _ N (I.Sb false) (I.Sb true) (I.LA τ nbar) hFrm hL (hE false) (hE true)
    (hSd false) (hSd true) hSz hRk hD0 hD1 (hMx hRows.2) ⟨hn, hM2⟩ hRows

end In

def Steps : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ)
    (I : In K G Pl0 T m), I.PRho ∧ I.PJ ∧ I.PRange ∧ I.PMet ∧ I.PFrames ∧ I.PUni ∧ I.PLat ∧ I.PGLat ∧ I.PSand ∧
      ∀ (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
        [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)), I.PGood τ

end Formalism.IndefR.CxPass
end
end

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

def rep (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) : Representation K G (Fin I.Sg.D → K) where
  toFun g := Matrix.toLin' (I.ρf g)
  map_one' := by rw [h1, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [hm, Matrix.toLin'_mul]; rfl

theorem rep_apply (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) (g : G) (x : Fin I.Sg.D → K) :
    I.rep h1 hm g x = I.ρf g *ᵥ x := by
  first
  | rfl
  | simp [rep, Matrix.toLin'_apply]

theorem epM_eq (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) (P : Subgroup G) (ψ : P →* Kˣ)
    (χ : P →* (𝓞 K)ˣ) (hχ : ∀ h, (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((ψ h : Kˣ) : K)) :
    (I.epM P ψ).mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP P χ (I.rep h1 hm) := by
  rw [← Matrix.toLin'_apply']
  simp only [epM, Formalism.IndefR.TransferLatticeStatement.epP, map_smul, map_sum, hχ, map_inv]
  congr 1
  refine Finset.sum_congr (by congr; exact Subsingleton.elim _ _) (fun h _ => ?_)
  have e := hχ h⁻¹
  rw [map_inv χ, map_inv ψ] at e
  rw [e]
  rfl

theorem eMat_eq (h1 : I.ρf 1 = 1) (hm : ∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) {W : Type} [AddCommGroup W]
    [Module K W] (τ : Representation K G W) :
    (I.eMat τ).mulVecLin = Formalism.IndefR.TransferLatticeStatement.eS τ (I.rep h1 hm) := by
  rw [← Matrix.toLin'_apply']
  simp only [eMat, Formalism.IndefR.TransferLatticeStatement.eS, map_smul, map_sum]
  rfl

theorem passage_of_steps [IsTotallyComplex K] {s : ℕ} (H : I.Hyp s) {S : Type} [Fintype S] {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) (N : IndefNum I.A3.fam3.base3)
    (hρ : I.PRho) (hJ : I.PJ) (hR : I.PRange) (hMet : I.PMet) (hFr : I.PFrames) (hU : I.PUni)
    (hLat : I.PLat) (hGL : I.PGLat) (hS : I.PSand) (hGood : I.PGood τ)
    (hτ : Formalism.IndefR.TransferLatticeStatement.IsGood τ) (hX : CharsX τ I.A.fam.X) (hM1 : Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨I.P0, I.ψ0⟩) (hn : 0 < nbar)
    (hM2 : NearConstantMultiplicities τ ⟨I.P1, I.ψ1⟩ nbar N.de) (hla : N.la = Formalism.IndefR.IndefiniteEpsilonOperator.la G) :
    Passage N (I.Sb false) (I.Sb true) := by
  obtain ⟨h1, hm, -⟩ := hρ s H
  obtain ⟨χ0, hχ0⟩ := Formalism.IndefR.LatticeTransfer.liftChar K I.P0 I.ψ0
  obtain ⟨χ1, hχ1⟩ := Formalism.IndefR.LatticeTransfer.liftChar K I.P1 I.ψ1
  have hFrm : (I.LA τ nbar).FramesG := hFr s H
  have hL : (I.LA τ nbar).LatG := hLat s H
  have key0 : (I.LA τ nbar).ep0.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P0 χ0 (I.rep h1 hm) :=
    I.epM_eq h1 hm I.P0 I.ψ0 χ0 hχ0
  have key1 : (I.LA τ nbar).ep1.mulVecLin = Formalism.IndefR.TransferLatticeStatement.epP I.P1 χ1 (I.rep h1 hm) :=
    I.epM_eq h1 hm I.P1 I.ψ1 χ1 hχ1
  have hs : ∀ t : S, (I.eMat (τ t)).mulVecLin = Formalism.IndefR.TransferLatticeStatement.eS (τ t) (I.rep h1 hm) := fun t =>
    I.eMat_eq h1 hm (τ t)
  have hnS : ∀ t : S, Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ t) ⟨I.P1, I.ψ1⟩ = Formalism.IndefR.TransferLatticeStatement.nS (τ t) I.P1 χ1 := fun t =>
    nOf_eq_nS (τ t) I.P1 I.ψ1 χ1 hχ1
  have hM1' : Formalism.IndefR.TransferLatticeStatement.M1 τ I.P0 χ0 := fun t => by rw [← nOf_eq_nS (τ t) I.P0 I.ψ0 χ0 hχ0]; exact hM1 t
  have hgood : Formalism.IndefR.TransferLatticeStatement.eGood τ (I.rep h1 hm) = LinearMap.id := by
    unfold Formalism.IndefR.TransferLatticeStatement.eGood
    rw [← Finset.sum_congr rfl fun t _ => hs t]
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun M : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K => M *ᵥ x) (hGood s H hτ hX)
    simp only [Matrix.sum_mulVec, Matrix.one_mulVec] at hx
    rw [LinearMap.sum_apply, LinearMap.id_apply]
    simpa only [Matrix.mulVecLin_apply] using hx
  have hst : ∀ g : G, ∀ a ∈ I.Sg.RR, I.rep h1 hm g a ∈ I.Sg.RR := fun g a ha => by
    rw [rep_apply]; exact hGL s H g a ha
  have hUn : Formalism.IndefR.TransferLatticeStatement.IsUnitaryRep (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE (I.rep h1 hm) := fun v g x y => by
    rw [rep_apply, rep_apply]; exact hU s H v g x y
  obtain ⟨hRk, hD0, hD1, hMx⟩ := Formalism.IndefR.LatticeTransfer.levelAmb_transfer (I.LA τ nbar) τ I.P0 χ0 I.P1 χ1 (I.rep h1 hm) hτ hM1'
    key0 key1 hs hnS rfl hgood hFrm hL hst hUn
  have hE : ∀ b, (I.LA τ nbar).EmbAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).XE := fun b =>
    ⟨(hJ s H b).2, hR s H b, hMet s H b⟩
  have hSd : ∀ b, (I.LA τ nbar).SandAt (I.Jm b) (I.epM (I.lvP b) (I.lvψ b)) (Nat.card (I.lvP b)) (I.Sb b).RR := by
    intro b
    obtain ⟨hin, hout⟩ := hS s H b
    refine ⟨?_, ?_⟩
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨hin x hx, ?_⟩
      show (I.Jm b *ᵥ x) ∈ LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin
      rw [← hR s H b]; exact ⟨x, rfl⟩
    · rintro y ⟨hyR, hyE⟩
      obtain ⟨x, hx, hxy⟩ := hout y hyR hyE
      exact ⟨x, hx, hxy⟩
  have hRows : (I.LA τ nbar).RowsG :=
    ⟨Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm false) _ H.pos0 (hJ s H false).2 (hR s H false),
      Formalism.L2.GlobalTheoryTheory.DivPassage2.rows_gen (I.LA τ nbar) hL (I.Jm true) _ H.pos1 (hJ s H true).2 (hR s H true)⟩
  have hSz : (I.LA τ nbar).Sizes N.la := by
    refine ⟨Nat.card_pos, ?_, Nat.card_pos, ?_, ?_⟩
    · exact (Subgroup.card_le_card_group I.P0).trans (Nat.card_eq_fintype_card).le
    · exact (Subgroup.card_le_card_group I.P1).trans (Nat.card_eq_fintype_card).le
    · rw [hla]; exact le_refl _
  exact passage_from_levels K I.A3.fam3.base3 _ _ N (I.Sb false) (I.Sb true) (I.LA τ nbar) hFrm hL (hE false) (hE true)
    (hSd false) (hSd true) hSz hRk hD0 hD1 (hMx hRows.2) ⟨hn, hM2⟩ hRows

end In3

def Steps3 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ)
    (I : In3 K G Pl0 I0 Ty T m), I.PRho ∧ I.PJ ∧ I.PRange ∧ I.PMet ∧ I.PFrames ∧ I.PUni ∧ I.PLat ∧ I.PGLat ∧ I.PSand ∧
      ∀ (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
        [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)), I.PGood τ

theorem cutPassage3S_of_steps (h : Steps3) : CutPassage3S := by
  intro K _ _ _ _ G _ _ Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S _ Ws _ _ _ τ nbar
    hok hsep hst hin h4 hp0 hp1 hh2 hrat hh2g hratg hgu hge hn0 hn1 hτ hX hM1 hn hM2 hla
  let I : In3 K G Pl0 I0 Ty T m := ⟨A3, P0, ψ0, P1, ψ1, Dc, Sp, Zsc, X, gE⟩
  obtain ⟨hρ, hJ, hR, hMet, hFr, hU, hLat, hGL, hS, hG⟩ := h K G Pl0 I0 Ty T m I
  exact I.passage_of_steps ⟨hok, hsep, hst, hin, h4, hp0, hp1, hh2, hrat, hh2g, hratg, hgu, hge, hn0, hn1⟩
    τ nbar _ hρ hJ hR hMet hFr hU hLat hGL hS (hG S Ws τ) hτ hX hM1 hn hM2 hla


end Formalism.IndefR.CxPass
end
end

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace PassRep

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0)

def cv (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) : Fin B.S.dim → K :=
  (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y)

theorem toF_eq (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y = B.S.basis.equivFun.symm (cv B ℓ Z y) := rfl

theorem cv_injective (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) : Function.Injective (cv B ℓ Z) := by
  intro x y h
  exact (subspace_image_spec K _ (B.Z0 ℓ Z)).1
    ((image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).1 h)

theorem cv_mulVec (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) {n : ℕ} (M : Matrix (Fin (B.dZ ℓ Z)) (Fin n) K)
    (x : Fin n → K) : cv B ℓ Z (M.mulVec x) = (B.vE ℓ * B.zE ℓ Z * M).mulVec x := by
  simp only [cv, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem mem_coord (Z : Submodule K B.S.Forms) (w : Fin B.S.dim → K) :
    w ∈ B.coord Z ↔ B.S.basis.equivFun.symm w ∈ Z := by
  unfold BlockDat.coord
  constructor
  · rintro ⟨f, hf, rfl⟩
    simpa using hf
  · intro h
    exact ⟨_, h, B.S.basis.equivFun.apply_symm_apply w⟩

theorem range_cv (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : Fin B.S.dim → K) :
    (∃ y, cv B ℓ Z y = w) ↔ w ∈ B.coord Z ∧ w ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
  have hs := (subspace_image_spec K _ (B.Z0 ℓ Z)).2
  constructor
  · rintro ⟨y, rfl⟩
    have hy : (B.zE ℓ Z).mulVec y ∈ B.Z0 ℓ Z := by
      rw [← hs]
      exact ⟨y, rfl⟩
    exact ⟨hy, ⟨_, rfl⟩⟩
  · rintro ⟨hZ, u, rfl⟩
    have hu : u ∈ B.Z0 ℓ Z := hZ
    rw [← hs] at hu
    obtain ⟨y, rfl⟩ := hu
    exact ⟨y, rfl⟩

theorem range_vE_bot (X : Finset (G → K)) :
    LinearMap.range (B.vE ⟨X, ⊥, 1⟩).mulVecLin = LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin := by
  have h := (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt X (⊥ : Subgroup G) 1))).2
  have hb : goodAt X (⊥ : Subgroup G) (1 : (⊥ : Subgroup G) →* Kˣ) = idemOf X := by
    unfold goodAt
    rw [level_idempotent_bot K G, mul_one]
  rw [← hb]
  exact h

theorem range_vE_le (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) :
    LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin ≤ LinearMap.range (B.vE ⟨X, ⊥, 1⟩).mulVecLin := by
  rw [range_vE_bot]
  have h := (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt X P ψ))).2
  change LinearMap.range (imE (B.S.gaMat B.r (goodAt X P ψ))).mulVecLin ≤ _
  rw [h]
  unfold goodAt
  rw [(group_action_matrix_hom K B.S G B.r).2, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

theorem range_vE_lvl (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) :
    LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (idemOf X)).mulVecLin ⊓ B.S.lvlPart B.r P ψ :=
  good_part_spec K B.S G B.r X hX P ψ

theorem toF_sub (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) (Z : Submodule K B.S.Forms)
    (x : Fin (B.dZ ⟨X, P, ψ⟩ Z) → K) :
    ∃ y : Fin (B.dZ ⟨X, ⊥, 1⟩ Z) → K, B.toF ⟨X, ⊥, 1⟩ Z y = B.toF ⟨X, P, ψ⟩ Z x := by
  obtain ⟨hZ, hV⟩ := (range_cv B ⟨X, P, ψ⟩ Z _).1 ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).2 ⟨hZ, range_vE_le B X P ψ hV⟩
  exact ⟨y, by rw [toF_eq, toF_eq, hy]⟩

theorem actMat_coord (g : G) (w : Fin B.S.dim → K) :
    (B.S.actMat B.r g).mulVec w = B.S.basis.equivFun (B.r g (B.S.basis.equivFun.symm w)) := by
  have h := LinearMap.toMatrix_mulVec_repr B.S.basis B.S.basis (B.r g) (B.S.basis.equivFun.symm w)
  have hx : (B.S.basis.repr (B.S.basis.equivFun.symm w) : Fin B.S.dim → K) = w := by
    rw [← Basis.equivFun_apply]
    exact B.S.basis.equivFun.apply_symm_apply w
  rw [hx] at h
  unfold CSD.actMat
  rw [h, Basis.equivFun_apply]

theorem coord_act (Z : Submodule K B.S.Forms) (g : G) (hZ : ∀ f ∈ Z, B.r g f ∈ Z) (w : Fin B.S.dim → K)
    (hw : w ∈ B.coord Z) : (B.S.actMat B.r g).mulVec w ∈ B.coord Z := by
  rw [mem_coord] at hw ⊢
  rw [actMat_coord, LinearEquiv.symm_apply_apply]
  exact hZ _ hw

theorem gaMat_single (g : G) : B.S.gaMat B.r (MonoidAlgebra.single g 1) = B.S.actMat B.r g := by
  rw [CSD.gaMat_eq_lift, MonoidAlgebra.lift_single, one_smul]
  rfl

theorem comm_idem (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (a : MonoidAlgebra K G) :
    B.S.gaMat B.r a * B.S.gaMat B.r (idemOf X) = B.S.gaMat B.r (idemOf X) * B.S.gaMat B.r a := by
  have hm := (group_action_matrix_hom K B.S G B.r).2
  rw [← hm, ← hm, (idempotent_central K G X hX).2 a]

theorem toF_act (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (Z : Submodule K B.S.Forms) (g : G)
    (hZ : ∀ f ∈ Z, B.r g f ∈ Z) (x : Fin (B.dZ ⟨X, ⊥, 1⟩ Z) → K) :
    ∃ y, B.toF ⟨X, ⊥, 1⟩ Z y = B.r g (B.toF ⟨X, ⊥, 1⟩ Z x) := by
  obtain ⟨hZx, hV⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).1 ⟨x, rfl⟩
  rw [range_vE_bot] at hV
  obtain ⟨w, hw⟩ := hV
  have h1 : (B.S.actMat B.r g).mulVec (cv B ⟨X, ⊥, 1⟩ Z x) ∈ LinearMap.range (B.vE ⟨X, ⊥, 1⟩).mulVecLin := by
    rw [range_vE_bot]
    refine ⟨(B.S.actMat B.r g).mulVec w, ?_⟩
    simp only [Matrix.mulVecLin_apply] at hw ⊢
    rw [← hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← gaMat_single, comm_idem B X hX]
  obtain ⟨y, hy⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).2 ⟨coord_act B Z g hZ _ hZx, h1⟩
  refine ⟨y, ?_⟩
  rw [toF_eq, toF_eq, hy, actMat_coord, LinearEquiv.symm_apply_apply]

end Block

section Rel

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cpt_single (σ : K →+* ℂ) {n : ℕ} (k : Fin n) : cpt σ (Pi.single k (1 : K)) = Pi.single k 1 := by
  funext i
  by_cases h : i = k <;> simp [cpt, h]

theorem relK (σ : K →+* ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] {D n : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E)
    (g : (Fin n → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f)
    (hg : ∀ x : Fin n → K, ∃ y : Fin D → K, f (cpt σ y) = g (cpt σ x)) :
    IsRat σ (relMat f g) ∧ ∀ x : Fin n → K, f (cpt σ ((kMat σ (relMat f g)).mulVec x)) = g (cpt σ x) := by
  have hk : ∀ k, g (Pi.single k 1) ∈ LinearMap.range f := fun k => by
    obtain ⟨y, hy⟩ := hg (Pi.single k 1)
    rw [cpt_single] at hy
    exact ⟨_, hy⟩
  have hrat : IsRat σ (relMat f g) := by
    intro i k
    obtain ⟨y, hy⟩ := hg (Pi.single k 1)
    rw [cpt_single] at hy
    have hs : solve f (g (Pi.single k 1)) = cpt σ y := hf (by rw [solve_spec f (hk k), hy])
    exact ⟨y i, by simp only [relMat, Matrix.of_apply, hs, cpt]⟩
  refine ⟨hrat, fun x => ?_⟩
  rw [cpt_mulVec, kMat_map σ hrat, relMat_spec f g hk]

theorem iC_cpt {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)
    (b : Bool) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, CxData.iC, lin_apply, cpt]

theorem key_row' {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc)
    (b : Bool) (hr : ∀ t, LinearMap.range (X.iC cr b t) = LinearMap.range (X.iC cr b Bs.μ0)) (hq : X.RATmu cr b)
    (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b Bs.μ0 (cpt Bs.v0.embedding ((X.rowMat cr b t).mulVec x)) = X.iC cr b t (cpt Bs.v0.embedding x) := by
  rw [cpt_mulVec, CxData.rowMat, kMat_map _ (hq t)]
  refine relMat_spec _ _ (fun k => ?_) _
  rw [← hr t]
  exact ⟨_, rfl⟩

end Rel

theorem mat_ext {K : Type} [Field K] {n k : ℕ} (M N : Matrix (Fin n) (Fin k) K) (h : ∀ x, M.mulVec x = N.mulVec x) :
    M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by simpa only [Matrix.toLin'_apply] using h x)

section Block2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0)

theorem cv_eq (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    cv B ℓ Z y = (B.vE ℓ * B.zE ℓ Z).mulVec y := by
  simp only [cv, Matrix.mulVec_mulVec]

theorem cv_of_toF {ℓ ℓ' : Lvl K G} {Z : Submodule K B.S.Forms} {x : Fin (B.dZ ℓ Z) → K} {y : Fin (B.dZ ℓ' Z) → K}
    (h : B.toF ℓ Z x = B.toF ℓ' Z y) : cv B ℓ Z x = cv B ℓ' Z y :=
  B.S.basis.equivFun.symm.injective h

theorem range_eq_block (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ)
    (Z : Submodule K B.S.Forms)
    (J : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, P, ψ⟩ Z)) K)
    (hJ : ∀ x, cv B ⟨X, ⊥, 1⟩ Z (J.mulVec x) = cv B ⟨X, P, ψ⟩ Z x)
    (Ep : Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) K)
    (hE : ∀ y, cv B ⟨X, ⊥, 1⟩ Z (Ep.mulVec y) =
      (B.S.gaMat B.r (lvlIdem P ψ)).mulVec (cv B ⟨X, ⊥, 1⟩ Z y)) :
    LinearMap.range J.mulVecLin = LinearMap.range Ep.mulVecLin := by
  have hinj := cv_injective B ⟨X, ⊥, 1⟩ Z
  have hlvl := range_vE_lvl B X hX P ψ
  ext z
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨J.mulVec x, hinj ?_⟩
    rw [hE, hJ]
    have hx : cv B ⟨X, P, ψ⟩ Z x ∈ B.S.lvlPart B.r P ψ := by
      have := ((range_cv B ⟨X, P, ψ⟩ Z _).1 ⟨x, rfl⟩).2
      rw [hlvl, Submodule.mem_inf] at this
      exact this.2
    exact B.S.lvlIdem_mulVec_of_mem B.r P ψ _ hx
  · rintro ⟨y, rfl⟩
    obtain ⟨hZ, -⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).1 ⟨Ep.mulVec y, rfl⟩
    have hV : cv B ⟨X, ⊥, 1⟩ Z (Ep.mulVec y) ∈ LinearMap.range (B.vE ⟨X, P, ψ⟩).mulVecLin := by
      rw [hlvl, hE, Submodule.mem_inf]
      obtain ⟨-, hy⟩ := (range_cv B ⟨X, ⊥, 1⟩ Z _).1 ⟨y, rfl⟩
      rw [range_vE_bot] at hy
      obtain ⟨u, hu⟩ := hy
      refine ⟨⟨(B.S.gaMat B.r (lvlIdem P ψ)).mulVec u, ?_⟩, ?_⟩
      · simp only [Matrix.mulVecLin_apply] at hu ⊢
        rw [← hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, comm_idem B X hX]
      · rw [← level_part_spec K B.S G B.r P ψ]
        exact ⟨_, rfl⟩
    obtain ⟨x, hx⟩ := (range_cv B ⟨X, P, ψ⟩ Z _).2 ⟨hZ, hV⟩
    exact ⟨x, hinj (by rw [hJ, hx])⟩

theorem cv_typeProj (X : Finset (G → K)) (Z : Submodule K B.S.Forms)
    (ρ : G → Matrix (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) (Fin (B.dZ ⟨X, ⊥, 1⟩ Z)) K)
    (hρ : ∀ g x, cv B ⟨X, ⊥, 1⟩ Z ((ρ g).mulVec x) = (B.S.actMat B.r g).mulVec (cv B ⟨X, ⊥, 1⟩ Z x))
    (P : Subgroup G) (ψ : P →* Kˣ) (y : Fin (B.dZ ⟨X, ⊥, 1⟩ Z) → K) :
    haveI : Fintype P := Fintype.ofFinite P
    cv B ⟨X, ⊥, 1⟩ Z ((((Nat.card P : K)⁻¹) • ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • ρ (h : G)).mulVec y) =
      (B.S.gaMat B.r (lvlIdem P ψ)).mulVec (cv B ⟨X, ⊥, 1⟩ Z y) := by
  classical
  have hC : ∀ g : G, B.vE ⟨X, ⊥, 1⟩ * B.zE ⟨X, ⊥, 1⟩ Z * ρ g =
      B.S.actMat B.r g * (B.vE ⟨X, ⊥, 1⟩ * B.zE ⟨X, ⊥, 1⟩ Z) := fun g =>
    mat_ext _ _ fun x => by
      have := hρ g x
      rw [cv_eq, cv_eq] at this
      rw [← Matrix.mulVec_mulVec (M := B.vE ⟨X, ⊥, 1⟩ * B.zE ⟨X, ⊥, 1⟩ Z) (N := ρ g), this, Matrix.mulVec_mulVec]
  rw [cv_eq, cv_eq, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [Matrix.mul_smul, Matrix.mul_sum, CSD.gaMat_lvlIdem, Matrix.sum_mul, Finset.smul_sum]
  refine Finset.sum_congr (Finset.eq_univ_of_forall fun x => @Finset.mem_univ _ (Fintype.ofFinite P) x) fun h _ => ?_
  simp only [Matrix.mul_smul, hC, Matrix.smul_mul, smul_smul, map_inv]

end Block2

section Lev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

theorem sub_lvl (b : Bool) (t : I.A.fam.base.Tup)
    (x : Fin ((lv (faceOf I.A I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t) → K) :
    ∃ y, I.cg.toR I.X.zs false t y = I.cr.toR I.X.zs b t x := by
  cases b
  · exact toF_sub (I.A.fam.R t) I.A.fam.X I.P0 I.ψ0 (I.X.zs.Z t) x
  · exact toF_sub (I.A.fam.R t) I.A.fam.X I.P1 I.ψ1 (I.X.zs.Z t) x

theorem jt_spec (h2g : PrincipalInjectiveCommonRange I.A I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)) (b : Bool) (t : I.A.fam.base.Tup) :
    (∀ x, I.X.iC I.cg false t (cpt I.A.fam.base.v0.embedding ((I.Jt b t).mulVec x)) =
      I.X.iC I.cr b t (cpt I.A.fam.base.v0.embedding x)) ∧
    ∀ x, I.cg.toR I.X.zs false t ((I.Jt b t).mulVec x) = I.cr.toR I.X.zs b t x := by
  have hinj : Function.Injective (I.X.iC I.cg false t) := (h2g.2 t).1
  have h1 : ∀ x, I.X.iC I.cg false t (cpt I.A.fam.base.v0.embedding ((I.Jt b t).mulVec x)) =
      I.X.iC I.cr b t (cpt I.A.fam.base.v0.embedding x) :=
    (relK _ (I.X.iC I.cg false t) (I.X.iC I.cr b t) hinj fun x => by
      obtain ⟨y, hy⟩ := sub_lvl I b t x
      exact ⟨y, by rw [iC_cpt, iC_cpt, hy]⟩).2
  refine ⟨h1, fun x => ?_⟩
  obtain ⟨y, hy⟩ := sub_lvl I b t x
  have e : (I.Jt b t).mulVec x = y := by
    apply cpt_injective I.A.fam.base.v0.embedding
    apply hinj
    rw [h1, iC_cpt, iC_cpt, hy]
  rw [e, hy]

theorem rho_y {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    ∃ y : Fin I.Sg.D → K, I.cg.toR I.X.zs false I.A.fam.base.μ0 y =
      (I.A.fam.R I.A.fam.base.μ0).r g (I.cg.toR I.X.zs false I.A.fam.base.μ0 x) := by
  have hZ : ∀ f ∈ I.X.zs.Z I.A.fam.base.μ0, (I.A.fam.R I.A.fam.base.μ0).r g f ∈ I.X.zs.Z I.A.fam.base.μ0 :=
    fun f hf => H.stable.1 _ (Sum.inr g) (Submodule.mem_map_of_mem hf)
  exact toF_act (I.A.fam.R I.A.fam.base.μ0) I.A.fam.X H.ok.irr (I.X.zs.Z I.A.fam.base.μ0) g hZ x

theorem iCg_of_y {s : ℕ} (H : I.Hyp s) (g : G) (x y : Fin I.Sg.D → K)
    (hy : I.cg.toR I.X.zs false I.A.fam.base.μ0 y =
      (I.A.fam.R I.A.fam.base.μ0).r g (I.cg.toR I.X.zs false I.A.fam.base.μ0 x)) :
    I.iCg (cpt I.A.fam.base.v0.embedding y) = I.gE g (I.iCg (cpt I.A.fam.base.v0.embedding x)) :=
  (iC_cpt I.X I.cg false _ y).trans ((congrArg (fun f => I.X.Θ I.A.fam.base.μ0 (I.X.jR I.A.fam.base.μ0 f)) hy).trans
    ((H.gequiv _ g _).trans (congrArg (I.gE g) (iC_cpt I.X I.cg false _ x).symm)))

theorem rho_spec {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    I.iCg (cpt I.A.fam.base.v0.embedding ((I.ρf g).mulVec x)) =
      I.gE g (I.iCg (cpt I.A.fam.base.v0.embedding x)) :=
  (relK _ I.iCg ((I.gE g).comp I.iCg) H.h2g.1 fun x => by
    obtain ⟨y, hy⟩ := rho_y I H g x
    exact ⟨y, iCg_of_y I H g x y hy⟩).2 x

theorem rho_cv {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) ((I.ρf g).mulVec x) =
      ((I.A.fam.R I.A.fam.base.μ0).S.actMat (I.A.fam.R I.A.fam.base.μ0).r g).mulVec
        (cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) x) := by
  obtain ⟨y, hy⟩ := rho_y I H g x
  have e : (I.ρf g).mulVec x = y :=
    cpt_injective _ (H.h2g.1 ((rho_spec I H g x).trans (iCg_of_y I H g x y hy).symm))
  rw [e, actMat_coord]
  have hy' : (I.A.fam.R I.A.fam.base.μ0).S.basis.equivFun.symm
      (cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) y) =
      (I.A.fam.R I.A.fam.base.μ0).r g ((I.A.fam.R I.A.fam.base.μ0).S.basis.equivFun.symm
        (cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) x)) := hy
  rw [← hy', LinearEquiv.apply_symm_apply]

theorem cv_epM {s : ℕ} (H : I.Hyp s) (P : Subgroup G) (ψ : P →* Kˣ) (y : Fin I.Sg.D → K) :
    cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) ((I.epM P ψ).mulVec y) =
      ((I.A.fam.R I.A.fam.base.μ0).S.gaMat (I.A.fam.R I.A.fam.base.μ0).r (lvlIdem P ψ)).mulVec
        (cv (I.A.fam.R I.A.fam.base.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A.fam.base.μ0) y) :=
  cv_typeProj (I.A.fam.R I.A.fam.base.μ0) I.A.fam.X (I.X.zs.Z I.A.fam.base.μ0) I.ρf (rho_cv I H) P ψ y

end Lev

end PassRep

namespace In

open Formalism.IndefR.CxPass.PassRep

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

theorem pJt : I.PJt := by
  intro s H b t
  obtain ⟨h1, h2⟩ := jt_spec I H.h2g b t
  refine ⟨h1, h2, fun x => ?_⟩
  apply cpt_injective I.A.fam.base.v0.embedding
  apply H.h2g.1
  exact ((jt_spec I H.h2g b I.A.fam.base.μ0).1 _).trans
    ((CxData.key_row I.X I.cr b (H.h2 b) (H.ratMu b) t x).trans
      ((h1 x).symm.trans (key_row' I.X I.cg false (fun t => (H.h2g.2 t).2) H.ratMug t _).symm))

theorem pRho : I.PRho := by
  intro s H
  have hinj : ∀ y y' : Fin I.Sg.D → K, I.iCg (cpt I.A.fam.base.v0.embedding y) =
      I.iCg (cpt I.A.fam.base.v0.embedding y') → y = y' :=
    fun y y' h => cpt_injective _ (H.h2g.1 h)
  refine ⟨mat_ext _ _ fun x => hinj _ _ ?_, fun g h => mat_ext _ _ fun x => hinj _ _ ?_, rho_spec I H⟩
  · exact (rho_spec I H 1 x).trans (by rw [Matrix.one_mulVec, map_one]; rfl)
  · calc I.iCg (cpt I.A.fam.base.v0.embedding ((I.ρf (g * h)).mulVec x))
        = I.gE (g * h) (I.iCg (cpt I.A.fam.base.v0.embedding x)) := rho_spec I H (g * h) x
      _ = I.gE g (I.gE h (I.iCg (cpt I.A.fam.base.v0.embedding x))) := by rw [map_mul]; rfl
      _ = I.gE g (I.iCg (cpt I.A.fam.base.v0.embedding ((I.ρf h).mulVec x))) :=
          congrArg (I.gE g) (rho_spec I H h x).symm
      _ = I.iCg (cpt I.A.fam.base.v0.embedding ((I.ρf g).mulVec ((I.ρf h).mulVec x))) :=
          (rho_spec I H g _).symm
      _ = I.iCg (cpt I.A.fam.base.v0.embedding ((I.ρf g * I.ρf h).mulVec x)) := by rw [Matrix.mulVec_mulVec]

theorem pJ : I.PJ := by
  intro s H b
  have h := (jt_spec I H.h2g b I.A.fam.base.μ0).1
  refine ⟨fun x => h x, fun x y hxy => ?_⟩
  apply cpt_injective I.A.fam.base.v0.embedding
  apply (H.h2 b).1
  exact (h x).symm.trans ((congrArg (fun v : Fin I.Sg.D → K => I.iCg (cpt I.A.fam.base.v0.embedding v)) hxy).trans (h y))

theorem pRange : I.PRange := by
  intro s H b
  cases b
  · exact range_eq_block (I.A.fam.R I.A.fam.base.μ0) I.A.fam.X H.ok.irr I.P0 I.ψ0 (I.X.zs.Z I.A.fam.base.μ0)
      (I.Jm false) (fun x => cv_of_toF _ ((jt_spec I H.h2g false I.A.fam.base.μ0).2 x))
      (I.epM I.P0 I.ψ0) (cv_epM I H I.P0 I.ψ0)
  · exact range_eq_block (I.A.fam.R I.A.fam.base.μ0) I.A.fam.X H.ok.irr I.P1 I.ψ1 (I.X.zs.Z I.A.fam.base.μ0)
      (I.Jm true) (fun x => cv_of_toF _ ((jt_spec I H.h2g true I.A.fam.base.μ0).2 x))
      (I.epM I.P1 I.ψ1) (cv_epM I H I.P1 I.ψ1)

end In

end Formalism.IndefR.CxPass
end
end

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace PassRep3

open Formalism.IndefR.CxPass.PassRep

section Lev

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

private lemma exists_toF_bot_eq_toF (B : BlockDat K G Pl0) (Xs : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
    (Z : Submodule K B.S.Forms) (x : Fin (B.dZ ⟨Xs, P, ψ⟩ Z) → K) :
    ∃ y : Fin (B.dZ ⟨Xs, ⊥, 1⟩ Z) → K, B.toF ⟨Xs, ⊥, 1⟩ Z y = B.toF ⟨Xs, P, ψ⟩ Z x := by
  classical
  have hS := fun n (W : Submodule K (Fin n → K)) => Formalism.L2.DIV.subspace_image_spec K n W
  obtain ⟨-, hmul⟩ := Formalism.L2.DIV.group_action_matrix_hom K B.S G B.r
  have hbot : lvlIdem (⊥ : Subgroup G) (1 : (⊥ : Subgroup G) →* Kˣ) = 1 := Formalism.L2.DIV.level_idempotent_bot K G 1
  have hu : B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x ∈ B.Z0 ⟨Xs, P, ψ⟩ Z := by
    rw [← (hS _ (B.Z0 ⟨Xs, P, ψ⟩ Z)).2]
    exact ⟨x, rfl⟩
  have hw : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈ B.coord Z := hu
  have hr1 : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈
      LinearMap.range (B.S.gaMat B.r (idemOf Xs)).mulVecLin := by
    have h0 : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈
        LinearMap.range (B.S.gaMat B.r (goodAt Xs P ψ)).mulVecLin := by
      rw [← (hS _ (LinearMap.range (B.S.gaMat B.r (goodAt Xs P ψ)).mulVecLin)).2]
      exact ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := h0
    refine ⟨B.S.gaMat B.r (lvlIdem P ψ) *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hmul]
    exact hv
  obtain ⟨u1, hu1⟩ : ∃ u1, B.vE ⟨Xs, ⊥, 1⟩ *ᵥ u1 = B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) := by
    have e : B.S.gaMat B.r (goodAt Xs ⊥ 1) = B.S.gaMat B.r (idemOf Xs) := by rw [goodAt, hbot, mul_one]
    have h1 : B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) ∈
        LinearMap.range (B.S.gaMat B.r (goodAt Xs ⊥ 1)).mulVecLin := by
      rw [e]
      exact hr1
    rw [← (hS _ (LinearMap.range (B.S.gaMat B.r (goodAt Xs ⊥ 1)).mulVecLin)).2] at h1
    obtain ⟨u1, hu1⟩ := h1
    exact ⟨u1, hu1⟩
  have hu1Z : u1 ∈ B.Z0 ⟨Xs, ⊥, 1⟩ Z := by
    show B.vE ⟨Xs, ⊥, 1⟩ *ᵥ u1 ∈ B.coord Z
    rw [hu1]
    exact hw
  rw [← (hS _ (B.Z0 ⟨Xs, ⊥, 1⟩ Z)).2] at hu1Z
  obtain ⟨y, hy⟩ := hu1Z
  refine ⟨y, ?_⟩
  have hy' : B.zE ⟨Xs, ⊥, 1⟩ Z *ᵥ y = u1 := hy
  have hin : B.vE ⟨Xs, ⊥, 1⟩ *ᵥ (B.zE ⟨Xs, ⊥, 1⟩ Z *ᵥ y) =
      B.vE ⟨Xs, P, ψ⟩ *ᵥ (B.zE ⟨Xs, P, ψ⟩ Z *ᵥ x) := by
    rw [hy', hu1]
  rw [BlockDat.toF_apply, BlockDat.toF_apply, hin]

theorem sub_lvl (b : Bool) (t : I.A3.fam3.base3.Tup)
    (x : Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t) → K) :
    ∃ y, I.cg.toR I.X.zs false t y = I.cr.toR I.X.zs b t x := by
  cases b
  · exact exists_toF_bot_eq_toF (I.A.fam.R t) I.A.fam.X I.P0 I.ψ0 (I.X.zs.Z t) x
  · exact exists_toF_bot_eq_toF (I.A.fam.R t) I.A.fam.X I.P1 I.ψ1 (I.X.zs.Z t) x

private lemma cpt_injective' (σ : K →+* ℂ) {n : ℕ} {x y : Fin n → K} (h : cpt σ x = cpt σ y) : x = y :=
  funext fun i => σ.injective (congrFun h i)

theorem jt_spec (h2g : PrincipalLevelBijectivity I.A3 I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)) (b : Bool) (t : I.A3.fam3.base3.Tup) :
    (∀ x, I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding ((I.Jt b t).mulVec x)) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x)) ∧
    ∀ x, I.cg.toR I.X.zs false t ((I.Jt b t).mulVec x) = I.cr.toR I.X.zs b t x := by
  have hg : ∀ x, ∃ y, I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding y) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b t x
    exact ⟨y, by rw [CxData.iC_cpt', CxData.iC_cpt', hy]⟩
  have hR := PassRep.relK I.A3.fam3.base3.v0.embedding (I.X.iC I.cg false t) (I.X.iC I.cr b t) (h2g.2 t).1 hg
  refine ⟨hR.2, fun x => ?_⟩
  obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b t x
  have h1 : I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding y) =
      I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding ((I.Jt b t).mulVec x)) := by
    rw [show I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding ((I.Jt b t).mulVec x)) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) from hR.2 x, CxData.iC_cpt', CxData.iC_cpt', hy]
  have h2 := cpt_injective' _ ((h2g.2 t).1 h1)
  rw [← h2, hy]

theorem rho_y {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    ∃ y : Fin I.Sg.D → K, I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 y =
      (I.A.fam.R I.A3.fam3.base3.μ0).r g (I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 x) := by
  have hX := H.ok.ok2.irr
  have hZ : ∀ f ∈ I.X.zs.Z I.A3.fam3.base3.μ0,
      (I.A.fam.R I.A3.fam3.base3.μ0).r g f ∈ I.X.zs.Z I.A3.fam3.base3.μ0 := fun f hf =>
    H.stable.1 _ (Sum.inr g) (Submodule.mem_map_of_mem hf)
  exact PassRep.toF_act (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X hX (I.X.zs.Z I.A3.fam3.base3.μ0) g hZ x

theorem iCg_of_y {s : ℕ} (H : I.Hyp s) (g : G) (x y : Fin I.Sg.D → K)
    (hy : I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 y =
      (I.A.fam.R I.A3.fam3.base3.μ0).r g (I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 x)) :
    I.iCg (cpt I.A3.fam3.base3.v0.embedding y) = I.gE g (I.iCg (cpt I.A3.fam3.base3.v0.embedding x)) := by
  show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) =
    I.gE g (I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x))
  erw [CxData.iC_cpt', CxData.iC_cpt', hy]
  exact H.gequiv _ g _

theorem rho_spec {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    I.iCg (cpt I.A3.fam3.base3.v0.embedding ((I.ρf g).mulVec x)) =
      I.gE g (I.iCg (cpt I.A3.fam3.base3.v0.embedding x)) := by
  have hg : ∀ x : Fin I.Sg.D → K, ∃ y : Fin I.Sg.D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding y) =
      ((I.gE g).comp I.iCg) (cpt I.A3.fam3.base3.v0.embedding x) := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.rho_y I H g x
    exact ⟨y, PassRep3.iCg_of_y I H g x y hy⟩
  exact (PassRep.relK I.A3.fam3.base3.v0.embedding I.iCg ((I.gE g).comp I.iCg) H.h2g.1 hg).2 x

theorem rho_cv {s : ℕ} (H : I.Hyp s) (g : G) (x : Fin I.Sg.D → K) :
    cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) ((I.ρf g).mulVec x) =
      ((I.A.fam.R I.A3.fam3.base3.μ0).S.actMat (I.A.fam.R I.A3.fam3.base3.μ0).r g).mulVec
        (cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) x) := by
  obtain ⟨y, hy⟩ := PassRep3.rho_y I H g x
  have hyeq : y = (I.ρf g).mulVec x :=
    cpt_injective' _ (H.h2g.1 ((PassRep3.iCg_of_y I H g x y hy).trans (PassRep3.rho_spec I H g x).symm))
  subst hyeq
  have key : ∀ v : Fin I.Sg.D → K,
      cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) v =
      (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun (I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 v) := by
    intro v
    show _ = (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun
      ((I.A.fam.R I.A3.fam3.base3.μ0).toF ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) v)
    erw [BlockDat.toF_apply, LinearEquiv.apply_symm_apply]
    rfl
  rw [key, key, hy]
  first
  | exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm
  | (simp only [Basis.equivFun_apply]; exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm)
  | (simp only [Basis.equivFun_apply, CSD.actMat]; exact (LinearMap.toMatrix_mulVec_repr _ _ _ _).symm)

theorem cv_epM {s : ℕ} (H : I.Hyp s) (P : Subgroup G) (ψ : P →* Kˣ) (y : Fin I.Sg.D → K) :
    cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) ((I.epM P ψ).mulVec y) =
      ((I.A.fam.R I.A3.fam3.base3.μ0).S.gaMat (I.A.fam.R I.A3.fam3.base3.μ0).r (lvlIdem P ψ)).mulVec
        (cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) y) := by
  classical
  let cvL : (Fin I.Sg.D → K) →ₗ[K] (Fin (I.A.fam.R I.A3.fam3.base3.μ0).S.dim → K) :=
    ((I.A.fam.R I.A3.fam3.base3.μ0).vE (⟨I.A.fam.X, ⊥, 1⟩ : Lvl K G)).mulVecLin ∘ₗ ((I.A.fam.R I.A3.fam3.base3.μ0).zE (⟨I.A.fam.X, ⊥, 1⟩ : Lvl K G) (I.X.zs.Z I.A3.fam3.base3.μ0)).mulVecLin
  have hcv : ∀ v : Fin I.Sg.D → K, cv (I.A.fam.R I.A3.fam3.base3.μ0) ⟨I.A.fam.X, ⊥, 1⟩ (I.X.zs.Z I.A3.fam3.base3.μ0) v = cvL v := fun v => rfl
  have e1 : I.epM P ψ *ᵥ y = ∑ h : P, (((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • (I.ρf (h : G) *ᵥ y)) := by
    rw [← Matrix.toLin'_apply, In3.epM]
    simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, Matrix.toLin'_apply,
      Finset.smul_sum, smul_smul, map_inv]
    congr 1
    all_goals first | rfl | exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
  have e2 : (I.A.fam.R I.A3.fam3.base3.μ0).S.gaMat (I.A.fam.R I.A3.fam3.base3.μ0).r (lvlIdem P ψ) *ᵥ cvL y =
      ∑ h : P, (((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) • ((I.A.fam.R I.A3.fam3.base3.μ0).S.actMat (I.A.fam.R I.A3.fam3.base3.μ0).r (h : G) *ᵥ cvL y)) := by
    rw [CSD.gaMat_lvlIdem, ← Matrix.toLin'_apply]
    simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, Matrix.toLin'_apply]
  rw [hcv, hcv, e1, e2, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, ← hcv, ← hcv, PassRep3.rho_cv I H (h : G) y]

end Lev

end PassRep3

namespace In3

open Formalism.IndefR.CxPass.PassRep Formalism.IndefR.CxPass.PassRep3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

private theorem iCg_cpt_Jm_mulVec_and_Jm_injective {s : ℕ} (H : I.Hyp s) (b : Bool) :
    (∀ x : Fin (I.Sb b).D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ x)) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x)) ∧ Function.Injective (I.Jm b).mulVec := by
  have hg : ∀ x : Fin (I.Sb b).D → K, ∃ y : Fin I.Sg.D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding y) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b I.A3.fam3.base3.μ0 x
    refine ⟨y, ?_⟩
    show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) = _
    erw [CxData.iC_cpt', CxData.iC_cpt', hy]
  have hR := PassRep.relK I.A3.fam3.base3.v0.embedding I.iCg (I.X.iC I.cr b I.A3.fam3.base3.μ0) H.h2g.1 hg
  refine ⟨hR.2, fun x y hxy => ?_⟩
  have h1 : I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) :=
    (hR.2 x).symm.trans ((congrArg (fun v => I.iCg (cpt I.A3.fam3.base3.v0.embedding v)) hxy).trans (hR.2 y))
  exact PassRep3.cpt_injective' _ ((H.h2 b).1 h1)

theorem pJt : I.PJt := by
  intro s H b t
  obtain ⟨h1, h2⟩ := PassRep3.jt_spec I H.h2g b t
  refine ⟨h1, h2, fun x => ?_⟩
  have e1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ (I.X.rowMat I.cr b t *ᵥ x))) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) :=
    ((iCg_cpt_Jm_mulVec_and_Jm_injective I H b).1 _).trans (PassRep.key_row' I.X I.cr b (fun t => ((H.h2 b).2.1 t).2) (H.ratMu b) t x)
  have e2 : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ x))) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x) :=
    (PassRep.key_row' I.X I.cg false (fun t => (H.h2g.2 t).2) H.ratMug t _).trans (h1 x)
  exact PassRep3.cpt_injective' _ (H.h2g.1 (e1.trans e2.symm))

theorem pRho : I.PRho := by
  intro s H
  have hsp := fun g x => PassRep3.rho_spec I H g x
  have hinj : ∀ M N : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K,
      (∀ x, I.iCg (cpt I.A3.fam3.base3.v0.embedding (M *ᵥ x)) = I.iCg (cpt I.A3.fam3.base3.v0.embedding (N *ᵥ x))) →
      M = N := by
    intro M N h
    have h' : ∀ x, M *ᵥ x = N *ᵥ x := fun x => PassRep3.cpt_injective' _ (H.h2g.1 (h x))
    exact Matrix.toLin'.injective (LinearMap.ext h')
  refine ⟨hinj _ _ fun x => ?_, fun g h => hinj _ _ fun x => ?_, hsp⟩
  · erw [hsp, Matrix.one_mulVec, map_one]
    rfl
  · erw [hsp, ← Matrix.mulVec_mulVec, hsp, hsp, map_mul]
    rfl

theorem pJ : I.PJ := by
  intro s H b
  exact iCg_cpt_Jm_mulVec_and_Jm_injective I H b

theorem pRange : I.PRange := by
  intro s H b
  have hX := H.ok.ok2.irr
  have hJt : ∀ x, I.cg.toR I.X.zs false I.A3.fam3.base3.μ0 (I.Jm b *ᵥ x) =
      I.cr.toR I.X.zs b I.A3.fam3.base3.μ0 x := by
    intro x
    obtain ⟨y, hy⟩ := PassRep3.sub_lvl I b I.A3.fam3.base3.μ0 x
    have h1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding y) = I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ x)) := by
      rw [(iCg_cpt_Jm_mulVec_and_Jm_injective I H b).1 x]
      show I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding y) = _
      erw [CxData.iC_cpt', CxData.iC_cpt', hy]
    have h2 := PassRep3.cpt_injective' _ (H.h2g.1 h1)
    rw [← h2, hy]
  have key : ∀ (ℓ : Lvl K G) (v : Fin ((I.A.fam.R I.A3.fam3.base3.μ0).dZ ℓ (I.X.zs.Z I.A3.fam3.base3.μ0)) → K),
      cv (I.A.fam.R I.A3.fam3.base3.μ0) ℓ (I.X.zs.Z I.A3.fam3.base3.μ0) v =
        (I.A.fam.R I.A3.fam3.base3.μ0).S.basis.equivFun
          ((I.A.fam.R I.A3.fam3.base3.μ0).toF ℓ (I.X.zs.Z I.A3.fam3.base3.μ0) v) := by
    intro ℓ v
    erw [BlockDat.toF_apply, LinearEquiv.apply_symm_apply]
    rfl
  cases b
  · refine PassRep.range_eq_block (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X hX I.P0 I.ψ0 (I.X.zs.Z I.A3.fam3.base3.μ0) (I.Jm false) (fun x => ?_)
      (I.epM I.P0 I.ψ0) (fun y => PassRep3.cv_epM I H I.P0 I.ψ0 y)
    rw [key, key]
    exact congrArg _ (hJt x)
  · refine PassRep.range_eq_block (I.A.fam.R I.A3.fam3.base3.μ0) I.A.fam.X hX I.P1 I.ψ1 (I.X.zs.Z I.A3.fam3.base3.μ0) (I.Jm true) (fun x => ?_)
      (I.epM I.P1 I.ψ1) (fun y => PassRep3.cv_epM I H I.P1 I.ψ1 y)
    rw [key, key]
    exact congrArg _ (hJt x)

end In3

end Formalism.IndefR.CxPass
end
end

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GoodPlacesAlt

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

theorem sum_chars_eq {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (Xc : Finset (G → K))
    (hinj : ∀ s t, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = Formalism.IndefR.TransferLatticeStatement.charOf (τ t) → s = t) (hX : CharsX τ Xc)
    {M : Type} [AddCommMonoid M] (F : (G → K) → M) :
    ∑ t, F (Formalism.IndefR.TransferLatticeStatement.charOf (τ t)) = ∑ χ ∈ Xc, F χ := by
  classical
  have himg : Finset.univ.image (fun t => Formalism.IndefR.TransferLatticeStatement.charOf (τ t)) = Xc := by
    ext χ
    rw [hX χ]
    simp
  rw [← himg, Finset.sum_image (fun s _ t _ h => hinj s t h)]

theorem mulVec_sum_smul {n : ℕ} (c : G → K) (M : G → Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (∑ g, c g • M g) *ᵥ x = ∑ g, c g • (M g *ᵥ x) := by
  classical
  have key : ∀ s : Finset G, (∑ g ∈ s, c g • M g) *ᵥ x = ∑ g ∈ s, c g • (M g *ᵥ x) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ← ih]
      first
        | rw [Matrix.smul_mulVec]
        | rw [Matrix.smul_mulVec_assoc]
        | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  exact key Finset.univ

theorem cpt_sum_smul (σ : K →+* ℂ) {n : ℕ} (c : G → K) (y : G → Fin n → K) :
    cpt σ (∑ g, c g • y g) = ∑ g, σ (c g) • cpt σ (y g) := by
  funext i
  simp [cpt, Finset.sum_apply, map_sum]

theorem sum_eq_one_of {E : Type} [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (f : (Fin n → ℂ) →ₗ[ℂ] E) (hf : Function.Injective f) (ρ : G → Matrix (Fin n) (Fin n) K)
    (act : G → E →ₗ[ℂ] E) (hρ : ∀ g x, f (cpt σ (ρ g *ᵥ x)) = act g (f (cpt σ x)))
    (c : G → K) (hfix : ∀ x, ∑ g, σ (c g) • act g (f (cpt σ x)) = f (cpt σ x)) :
    ∑ g, c g • ρ g = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
  have h1 : f (cpt σ ((∑ g, c g • ρ g) *ᵥ x)) = f (cpt σ x) := by
    rw [mulVec_sum_smul, cpt_sum_smul, map_sum]
    simp only [map_smul, hρ]
    exact hfix x
  have h2 := hf h1
  funext i
  exact σ.injective (congrFun h2 i)

end GoodPlacesAlt

namespace In

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (I : In K G Pl0 T m)

theorem sum_eMat_eq {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s))
    (hinj : ∀ s t, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = Formalism.IndefR.TransferLatticeStatement.charOf (τ t) → s = t) (hX : CharsX τ I.A.fam.X) :
    ∑ t, I.eMat (τ t) = ∑ g : G, (idemOf I.A.fam.X).coeff g • I.ρf g := by
  classical
  have hc : ∀ g : G, (idemOf I.A.fam.X).coeff g =
      ∑ χ ∈ I.A.fam.X, χ 1 / (Fintype.card G : K) * χ g⁻¹ := by
    intro g
    simp [idemOf, chiIdem, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply,
      Finsupp.single_apply]
  simp only [eMat]
  rw [GoodPlacesAlt.sum_chars_eq τ I.A.fam.X hinj hX
    (fun χ => (χ 1 / (Fintype.card G : K)) • ∑ x : G, χ x⁻¹ • I.ρf x)]
  simp only [hc, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem iCg_cpt (x : Fin ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A.fam.base.μ0) → K) :
    I.X.iC I.cg false I.A.fam.base.μ0 (cpt I.A.fam.base.v0.embedding x) =
      I.X.Θ I.A.fam.base.μ0 (I.X.jR I.A.fam.base.μ0
        ((I.A.fam.R I.A.fam.base.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.base.μ0) x)) := by
  rw [CxData.iC_eq_comp, CxData.lin_uQ_cpt]
  rfl

theorem idemOf_fix {s : ℕ} (hok : I.A.fam.Ok s)
    (x : Fin ((I.A.fam.R I.A.fam.base.μ0).dZ (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.base.μ0)) → K) :
    ∑ g : G, (idemOf I.A.fam.X).coeff g •
        (I.A.fam.R I.A.fam.base.μ0).r g ((I.A.fam.R I.A.fam.base.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.base.μ0) x) =
      (I.A.fam.R I.A.fam.base.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.base.μ0) x := by
  have hgood : goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ = idemOf I.A.fam.X := by
    show idemOf I.A.fam.X * lvlIdem ⊥ 1 = _
    rw [level_idempotent_bot K G 1, mul_one]
  have hidem : goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ *
      goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ =
      goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ := by
    rw [hgood]
    exact (idempotent_central K G I.A.fam.X hok.irr).1
  have h : (I.A.fam.R I.A.fam.base.μ0).S.gaOp (I.A.fam.R I.A.fam.base.μ0).r
        (goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ)
        ((I.A.fam.R I.A.fam.base.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.base.μ0) x) =
      (I.A.fam.R I.A.fam.base.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.base.μ0) x :=
    BlockDat.gaOp_fix (I.A.fam.R I.A.fam.base.μ0) (I.A.fam.lvl ⊥ 1) hidem
      (((I.A.fam.R I.A.fam.base.μ0).zE (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A.fam.base.μ0)).mulVec x)
  rw [hgood] at h
  conv_rhs => rw [← h]
  simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply]

theorem iCg_fix {s : ℕ} (hH : I.Hyp s)
    (x : Fin ((lv (faceOf I.A ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A.fam.base.μ0) → K) :
    ∑ g : G, I.A.fam.base.v0.embedding ((idemOf I.A.fam.X).coeff g) •
        I.gE g (I.X.iC I.cg false I.A.fam.base.μ0 (cpt I.A.fam.base.v0.embedding x)) =
      I.X.iC I.cg false I.A.fam.base.μ0 (cpt I.A.fam.base.v0.embedding x) := by
  have hq : ∀ (g : G) (f : I.A.fam.amb.FR I.A.fam.base.μ0),
      I.gE g (I.X.Θ I.A.fam.base.μ0 (I.X.jR I.A.fam.base.μ0 f)) =
        I.X.Θ I.A.fam.base.μ0 (I.X.jR I.A.fam.base.μ0 ((I.A.fam.R I.A.fam.base.μ0).r g f)) :=
    fun g f => (hH.gequiv I.A.fam.base.μ0 g f).symm
  rw [I.iCg_cpt x]
  simp_rw [hq]
  conv_rhs => rw [← I.idemOf_fix hH.ok x]
  simp only [map_sum, LinearMap.map_smulₛₗ, map_smul]

theorem pGood_of_rho (hρ : I.PRho) {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) : I.PGood τ := by
  intro s hH hG hX
  rw [I.sum_eMat_eq τ hG.2.2.2 hX]
  obtain ⟨-, -, hρg⟩ := hρ s hH
  exact GoodPlacesAlt.sum_eq_one_of I.A.fam.base.v0.embedding I.iCg hH.h2g.1 I.ρf (fun g => I.gE g) hρg
    (fun g => (idemOf I.A.fam.X).coeff g) (fun x => I.iCg_fix hH x)

theorem pGood_of (_hJt : I.PJt) (hρ : I.PRho) {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) : I.PGood τ := pGood_of_rho I hρ τ

end In

end Formalism.IndefR.CxPass
end
end

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

theorem sum_eMat_eq {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s))
    (hinj : ∀ s t, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = Formalism.IndefR.TransferLatticeStatement.charOf (τ t) → s = t) (hX : CharsX τ I.A.fam.X) :
    ∑ t, I.eMat (τ t) = ∑ g : G, (idemOf I.A.fam.X).coeff g • I.ρf g := by
  classical
  have hc : ∀ g : G, (idemOf I.A.fam.X).coeff g =
      ∑ χ ∈ I.A.fam.X, χ 1 / (Fintype.card G : K) * χ g⁻¹ := by
    intro g
    simp [idemOf, chiIdem, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply,
      Finsupp.single_apply]
  simp only [eMat]
  rw [GoodPlacesAlt.sum_chars_eq τ I.A.fam.X hinj hX
    (fun χ => (χ 1 / (Fintype.card G : K)) • ∑ x : G, χ x⁻¹ • I.ρf x)]
  simp only [hc, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem iCg_cpt (x : Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A3.fam3.base3.μ0) → K) :
    I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) =
      I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0
        ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x)) := by
  rw [CxData.iC_eq_comp, CxData.lin_uQ_cpt]
  rfl

theorem idemOf_fix {s : ℕ} (hok : I.A.fam.Ok s)
    (x : Fin ((I.A.fam.R I.A3.fam3.base3.μ0).dZ (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0)) → K) :
    ∑ g : G, (idemOf I.A.fam.X).coeff g •
        (I.A.fam.R I.A3.fam3.base3.μ0).r g ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x) =
      (I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x := by
  have hgood : goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ = idemOf I.A.fam.X := by
    show idemOf I.A.fam.X * lvlIdem ⊥ 1 = _
    rw [level_idempotent_bot K G 1, mul_one]
  have hidem : goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ *
      goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ =
      goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ := by
    rw [hgood]
    exact (idempotent_central K G I.A.fam.X hok.irr).1
  have h : (I.A.fam.R I.A3.fam3.base3.μ0).S.gaOp (I.A.fam.R I.A3.fam3.base3.μ0).r
        (goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ)
        ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x) =
      (I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x :=
    BlockDat.gaOp_fix (I.A.fam.R I.A3.fam3.base3.μ0) (I.A.fam.lvl ⊥ 1) hidem
      (((I.A.fam.R I.A3.fam3.base3.μ0).zE (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0)).mulVec x)
  rw [hgood] at h
  conv_rhs => rw [← h]
  simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply]

theorem iCg_fix {s : ℕ} (hH : I.Hyp s)
    (x : Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A3.fam3.base3.μ0) → K) :
    ∑ g : G, I.A3.fam3.base3.v0.embedding ((idemOf I.A.fam.X).coeff g) •
        I.gE g (I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x)) =
      I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) := by
  have hq : ∀ (g : G) (f : I.A3.fam3.amb3.FR I.A3.fam3.base3.μ0),
      I.gE g (I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0 f)) =
        I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0 ((I.A.fam.R I.A3.fam3.base3.μ0).r g f)) :=
    fun g f => (hH.gequiv I.A3.fam3.base3.μ0 g f).symm
  have hq' : ∀ g : G, I.gE g (I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0
      ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x))) =
      I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0 ((I.A.fam.R I.A3.fam3.base3.μ0).r g
        ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x))) := fun g => hq g _
  rw [I.iCg_cpt x]
  simp_rw [hq']
  conv_rhs => rw [← I.idemOf_fix hH.ok.ok2 x]
  erw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  erw [LinearMap.map_smulₛₗ, map_smul]
  first | done | rfl

theorem pGood_of_rho (hρ : I.PRho) {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) : I.PGood τ := by
  intro s hH hG hX
  rw [I.sum_eMat_eq τ hG.2.2.2 hX]
  obtain ⟨-, -, hρg⟩ := hρ s hH
  exact GoodPlacesAlt.sum_eq_one_of I.A3.fam3.base3.v0.embedding I.iCg hH.h2g.1 I.ρf (fun g => I.gE g) hρg
    (fun g => (idemOf I.A.fam.X).coeff g) (fun x => I.iCg_fix hH x)

theorem pGood_of (_hJt : I.PJt) (hρ : I.PRho) {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) : I.PGood τ := pGood_of_rho I hρ τ

end In3

end Formalism.IndefR.CxPass
end
end

section
namespace Formalism.IndefR.CxPass

theorem steps3 : Steps3 := fun _ _ _ _ _ _ _ _ _ _ _ _ I =>
  ⟨I.pRho, I.pJ, I.pRange, I.pMet_of I.pJt I.pJ, I.pFrames, I.pUni_of I.pJt I.pRho, I.pLat_of I.pJt,
    I.pGLat_of I.pJt I.pRho, I.pSand_of I.pJt I.pJ I.pRho I.pRange, fun _ _ _ _ _ _ τ => I.pGood_of I.pJt I.pRho τ⟩

theorem cutPassage3S : CutPassage3S := cutPassage3S_of_steps steps3


end Formalism.IndefR.CxPass
end

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

structure CxPassIn3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (X : CxData A3.fam3.amb3) (C CH : ℝ)
    (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) : Prop where

  ratMuP : X.RATmu (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false

  isGood : Formalism.IndefR.TransferLatticeStatement.IsGood τ

  chars : Formalism.IndefR.CxPass.CharsX τ A3.A.fam.X

  m1 : Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩

  nbarPos : 0 < nbar

  near_constant_multiplicities : Formalism.IndefR.CxPass.NearConstantMultiplicities τ ⟨P1, ψ1⟩ nbar ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).de

  laTie : ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).la = Formalism.IndefR.IndefiniteEpsilonOperator.la G

section Pass3

variable [IsTotallyComplex K] {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G}
  {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {X : CxData A3.fam3.amb3} {s : ℕ} {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {eV : ∀ t, (Fin ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Df1.nV t) → K) →ₗ[K] A3.fam3.amb3.FR t}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH} {C CH : ℝ}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)} {cf : ConvFace A3.fam3.base3}
  {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
  [∀ s, FiniteDimensional K (Ws s)] {τ : ∀ s, Representation K G (Ws s)} {nbar : ℝ}

theorem passage3_of (hN : PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf)
    (hP : CxPassIn3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH S Ws τ nbar) :
    Passage ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
      (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true) :=
  Formalism.IndefR.CxPass.cutPassage3S K G Pl0 I0 Ty T m A3 s P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH gE S Ws τ nbar hN.ok hN.sep
    hN.stable hN.inBlock hN.h4pos (hN.pos false) (hN.pos true) (fun b => (hN.what₂ b).1) hN.ratMu hN.h2P hP.ratMuP
    hN.gUnit hN.gEquiv hN.npTie.1 hN.npTie.2 hP.isGood hP.chars hP.m1 hP.nbarPos hP.near_constant_multiplicities hP.laTie

def packageFullHecke (hN : PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf)
    (hP : CxPassIn3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X C CH S Ws τ nbar) :
    IndefPkgR A3.fam3.amb3 (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH :=
  basePackageFullHecke { toPrimitiveStatementsBaseLiftsOnly := hN, passage := passage3_of hN hP }

end Pass3

end Formalism.IndefR.Cx
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section End3

open Formalism.IndefR.Cx Formalism.L2.Geo Formalism.MainNotions

variable [IsTotallyComplex D.what₂.LL] {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def PassIn3 (R : RealDat3 D A3 Ks) (F : Face3 D A3) (C CH : ℝ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (Ws : S → Type) (_ : ∀ s, AddCommGroup (Ws s)) (_ : ∀ s, Module D.what₂.LL (Ws s))
    (_ : ∀ s, FiniteDimensional D.what₂.LL (Ws s)) (τ : ∀ s, Representation D.what₂.LL G (Ws s)) (nbar : ℝ),
    CxPassIn3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc (R.toCx3 F) C CH S Ws τ nbar

def primitivePackageFullHecke {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (H : HkDat3 A3) (C CH : ℝ) (hC : R.WeakCharacterisation F)
    (hP : CovolumeOntoIsometryConditions R F sEE H C CH) (hI : PassIn3 R F C CH) :
    IndefPkgR A3.fam3.amb3 (faceOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) (R.convOf F H) C CH :=
  letI := hI.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose_spec.choose
  letI := hI.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  packageFullHecke (base_lifts_package_of_primitive_links hOk hsep hC hP) hI.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

def primRows3 {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F)
    (hP : PrimRows3 R F) : IndefRows (lv (F.fc (R.toCx3 F).zs) false) :=
  indefiniteDataAtBaseLevel (complex_data_conditions_base_level_of_primitive_links hOk hsep hC hP)

theorem primRows3_data {s : ℕ} (hOk : A3.fam3.Ok3 s) (hsep : A3.fam3.TypesSep3) {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    (hC : R.WeakCharacterisation F) (hP : PrimRows3 R F) : (primRows3 hOk hsep R F hC hP).toIndefData = (R.toCx3 F).data F.cr false := rfl

end End3

end Formalism.IndefR.Links

end
end
