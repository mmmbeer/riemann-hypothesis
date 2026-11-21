import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumns

section
noncomputable section

namespace GlobalTheory.TwU.AtTrue.Cl

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : ChainCharts D u μ)
  (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E)

variable {t u μ St A dtU a}

end Gen

section Std

open GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {Kc : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC}
  {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
  (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi)
  (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (K : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi))

structure IsStd (A : AdData t u a (charts I l Z u a bad Ch chOf eY K)) : Prop where
  crd : ∀ i hi, A.crd i hi = 1
  iA : HEq A.iA (RingEquiv.refl (AfE B.host.F B.host.E))
  q : HEq A.q ((QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E)))
  pt : HEq A.pt (fun i (_ : i ≤ B.R.m) (c : (I.stp u a i).Cl) => ((I.stp u a i).rep c).1.1)
  yb : HEq A.yb (fun c : (I.stp u a (B.R.m - 2 + 1)).Cl => ((I.stp u a (B.R.m - 2 + 1)).rep c).1.2)
  ib : ∀ i (hi : i < B.R.m) (c : (I.stp u a i).Cl), HEq (A.ib i hi (chOf i hi.le c)) (Idx.get c.1 hi)
  fb : ∀ i hi β P, A.fb i hi β P = 1
  y0 : ∀ (h : B.R.m - 2 + 1 ≤ B.R.m) (c : (I.stp u a (B.R.m - 2 + 1)).Cl) (P : rowSG (B.primes X) I.sel (I.tup a))
    (β : (charts I l Z u a bad Ch chOf eY K (t.m2 + 1) (cpl_lt t a).le).Ch) (P' : SB t a),
    HEq β (chOf (B.R.m - 2 + 1) h c) → HEq P' P → (cosetIn ((I.stp u a (B.R.m - 2 + 1)).rep c) P).Nonempty →
      ∃ y ∈ cosetIn ((I.stp u a (B.R.m - 2 + 1)).rep c) P, HEq (A.y0 β P') y

def Hyp (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) (A : AdData t u a (charts I l Z u a bad Ch chOf eY K)) : Prop :=
  I.Ok ∧ TC.Pins B X ∧ StdData I l Z t dt ∧ Side I l Z u a bad Ch chOf eY K ∧ (∀ i hi, ReadsOne I l Z u a i hi (chOf i hi) (K i hi)) ∧
    IsStd I l Z t u a bad Ch chOf eY K A

end Std

section Pf

open GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE

end Pf

end GlobalTheory.TwU.AtTrue.Cl

end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue GlobalTheory.TwU.AtTrue.Cl
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue.Cl

open Classical in

theorem sameCoset_of_mem_cosetIn {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p : PtAt R sel mu cst u j)
    (h : j + 1 = R.m) (P : rowSG Pr sel mu) {z z' : Sp X.E (R.N j)} (hz : z ∈ cosetIn p P) (hz' : z' ∈ cosetIn p P) :
    SameCoset sel mu cst P z z' := by
  obtain ⟨w, hw, hzw⟩ := hz
  obtain ⟨w', hw', hzw'⟩ := hz'
  obtain ⟨y, -, hY⟩ := p.mem_ybSet h
  rw [hY] at hw hw'
  have hww : w - w' ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
    have e1 : w - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := hw
    have e2 : w' - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := hw'
    have := sub_mem e1 e2
    rwa [sub_sub_sub_cancel_right] at this
  have h1 := (mem_locLat _ _ _ _).1 hww P
  set F := frsF sel mu p.1.1 P with hF
  set c : X.E := ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ with hc
  have hc' : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ = c := by
    rw [hc]; split_ifs <;> simp
  simp only [hc'] at h1
  have hFm : ∀ x, F x ∈ p.1.1.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
    intro x
    rw [hF]
    unfold frsF
    split_ifs with hP
    · exact (Deco.liftFr_spec (Deco.Ok.hasLift p.1.1.deco.2 ⟨P.1, hP⟩)).1 x
    · exact p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ x
  have h2 : c • (F.symm w - F.symm w') ∈ stdAt X.E (R.N j) P.1 := by
    rw [← map_sub, ← map_smul]
    apply (hFm _).1
    rw [LinearEquiv.apply_symm_apply]
    exact h1
  have h3 : c • (z - z') = c • (z - F.symm w) - c • (z' - F.symm w') + c • (F.symm w - F.symm w') := by
    rw [← smul_sub, ← smul_add]
    congr 1
    abel
  have h4 : c • (z - z') ∈ stdAt X.E (R.N j) P.1 := by
    rw [h3]
    exact add_mem (sub_mem hzw hzw') h2
  intro l
  have h5 := (ciMem_stdAt _ _).1 h4 l
  rw [Pi.smul_apply, smul_eq_mul] at h5
  exact h5

end GlobalTheory.TwU.AtTrue.Cl

namespace GlobalTheory.TwU.AtTrue.Cl

end GlobalTheory.TwU.AtTrue.Cl
end
