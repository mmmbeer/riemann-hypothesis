import Formalism.LocalToGlobal.Columns.RecChainUnfOne
import Formalism.LocalToGlobal.Columns.DetChrOf
import Formalism.LocalToGlobal.Columns.WordFin
import Formalism.LocalToGlobal.Columns.TiedBack
import Formalism.LocalToGlobal.Columns.ColumnDeterminants.ColsTiedD
import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.GlobalTheory.WindowConstantGeSixteen

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace Formalism.L2.Col

namespace DetChrOf

section Pull

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K]

def chiPull (σ : E →ₐ[F] E) (c : Formalism.L2.DIV.Chr F E K) : Formalism.L2.DIV.Chr F E K := c.comp (Formalism.L2.DIV.h90 σ)

end Pull

section Comparison₂

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)


end Comparison₂

section Amb

open Formalism.L2.Ker

variable {D : D7} {X : Fields} (s : Seam D X)

end Amb

end DetChrOf

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

structure ColJoint (c : ColRec) (C : ColObj c.what₂.LL c.what₂.Word) where
  isoF : ∀ u, Formalism.L2.GlobalTheoryTheory.HLatOps.Iso ((c.fm u).lat 0) (C.Mf u)
  ram : ∀ u, ((c.fm u).ramSub).map (isoF u).e.toLinearMap = LinearMap.range (C.incl u)
  T_eq : ∀ u, (c.mem u).A.T = C.T u
  f_eq : C.f = c.R.f
  k_eq : C.k = c.R.k
  m_eq : C.m = c.R.m
  Dstar_eq : ∀ u, (c.mem u).A.Dstar = C.Dstar

  duStar_eq : ∀ u, ((c.mem u).A.duStar : ℝ) = C.dstar u

def ColObj.onRec (D : D7) {c : ColRec} (h : D.colRec = c) (C : ColObj c.what₂.LL c.what₂.Word) : ColObj D.what₂.LL D.what₂.Word := by
  subst h
  exact C

def ColJoint.onRec (D : D7) {c : ColRec} (h : D.colRec = c) {C : ColObj c.what₂.LL c.what₂.Word} (J : ColJoint c C) :
    ColJoint D.colRec (ColObj.onRec D h C) := by
  subst h
  exact J

structure ColObj.InclOk {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} (C : ColObj K I) : Prop where
  inj : ∀ u, Function.Injective (C.incl u)
  norm : ∀ u v (x : (C.M u).V),
    Formalism.HermitianLatticesTheory.normAt (C.M u).b (C.M u).X v x = Formalism.HermitianLatticesTheory.normAt (C.Mf u).b (C.Mf u).X v (C.incl u x)
  L : ∀ u, (C.M u).L = (C.Mf u).L.comap ((C.incl u).restrictScalars (𝓞 K))

def NuTie (D : D7) (C : ColObj D.what₂.LL D.what₂.Word) (J : ColJoint D.colRec C) : Prop :=
  ∀ u, (D.div.Nu u).L.map ((((J.isoF u).e.toLinearMap).comp (D.nuIn u)).restrictScalars (𝓞 D.what₂.LL)) =
    (C.Npr u).map ((C.incl u).restrictScalars (𝓞 D.what₂.LL))

set_option maxHeartbeats 1000000 in

def concObj (d : ColDat) (a : ColArgs d) (A : ColArg (Pr := d.Pr) d.W d.Ch) : ColObj (d.colRec a).what₂.LL (d.colRec a).what₂.Word :=
  colObj d.W d.Ch d.hX A

section Ker

open Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {S : Set ℕ} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))

theorem twistPrimes_trivialTuple_empty_target : QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime (1 : Chr X.F X.E X.K) = ∅ := by
    ext v
    simp [Qprime]
  show QE sel (1 : Chr X.F X.E X.K) = ∅
  unfold QE
  rw [dif_pos (by rw [h]; exact Set.finite_empty)]
  simp [h]

theorem target_not_mem_qe (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∉ QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) := by
  rw [twistPrimes_trivialTuple_empty_target]
  exact Finset.notMem_empty P

end Ker

section KerRef

open Formalism.L2.Ker Formalism.MainNotions

variable {d : ColDat} (a : ColArgs d) {S : Set ℕ} (sel : HeightOneSpectrum (𝓞 d.X.F) → HeightOneSpectrum (𝓞 d.X.E))

structure KerAmbTied (D : D7) (X : Fields) (σ₀ : X.K →+* ℂ) where
  cc : Ideal (𝓞 D.host.K)
  cc_rec : cc = D.host.ccK
  cc_ok : TaylorLogMetric.IsCurveIdeal D cc
  δ : ℂ
  δ_ok : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ
  B : Base D cc δ
  B_std : B.StdOK
  χ : TaylorLogMetric.IdE D → ℂ
  χ_ok : TaylorLogMetric.IsChi D χ
  idl : D.Dt ⧸ D.UO → TaylorLogMetric.IdE D
  idl_ok : TaylorLogMetric.RelDetPinned D idl
  χ_rec : χ = TaylorLogMetric.chiRec D idl
  cD : D.what₂.Tau → ℂ
  cD_ok : IsDgen D cD
  seam : Seam D X
  seam_ok : seam.Ok
  seam_σ : seam.σ₀ = σ₀

def KerAmbTied.amb {D : D7} {X : Fields} {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) : Amb X := ambOf K.seam K.B K.χ K.cD

end KerRef

section Target

open Formalism.L2.GlobalTheoryTheory.ColOpen Formalism.L2.Ker

set_option maxHeartbeats 400000 in

def ColumnsAgreeAt (d : ColDat) (a : ColArgs d) (A : ColArg (Pr := d.Pr) d.W d.Ch) (D : D7) (h : D.colRec = d.colRec a) : Prop :=
  V1.ColHyp d → Nonempty (Formalism.L2.Forms.ColsTied D) ∧
    (Dat.Ok { R := d.R, X := d.X, sig0 := d.σ₀, Pr := d.Pr, Ch := d.Ch, W := d.W, a := A.num.sc.a } →
    Formalism.HermitianLatticesTheory.IsCMUnram d.X.E → MassRatioStd → d.X.f ≤ d.R.k →
    ∀ {Δ : ℝ} {c : d.X.Tau → ℝ} {code : d.Pr.Word → ℕ → ℕ}, Grid (Pr := d.Pr) d.W Δ A.num.Sc c code →
    Ends (Pr := d.Pr) d.W A.num.sc.a A.num.sc.b' A.num.Sc →
    Nodes (Pr := d.Pr) d.W A.num.sc.x A.num.sc.L A.num.eta A.num.Sc → Nums5 d.X d.Pr d.R A.num → NumsZ d.X d.R A.num (logAvC d.X A.num) →
    (∀ u, InWindow d.W d.Ch A.dsig d.num.GamP u) →
    (∀ u, MaxSlopeSummandWithConstant d.W d.Ch u A.num.C0) → ColArgOk d.W d.Ch A →
    ∃ I : ColIface (d.colRec a).what₂.LL (d.colRec a).what₂.Word, I.toColObj = concObj d a A ∧
      ∀ (J : ColJoint D.colRec (ColObj.onRec D h (concObj d a A))), NuTie D (ColObj.onRec D h (concObj d a A)) J →
        Nonempty ((ColObj.onRec D h I.toColObj).RecJoint D) ∧
        ∀ u, ((D.mem u).A.duStar : ℝ) = (ColObj.onRec D h I.toColObj).dstar u ∧
          (D.mem u).A.Xu = (ColObj.onRec D h I.toColObj).Xu u)

end Target

end Formalism.L2.Col
end
end

section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.Col

namespace DetChrChi

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

def ChiReads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word) : Prop :=
  ∀ j (cl : StCl W Λ u j), ∃ y : D.Dt,
    ((D.chiD y : ℂˣ) : ℂ) = σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) ∧
      K.idl (QuotientGroup.mk y) = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (R.N j)) (K.seam.lat (repN W Λ u j cl))



section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem carries_globLat (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    Formalism.L2.Herm.Carries g (stdLat E n) (Formalism.UG.CS.globLat g (stdLat E n)) := fun x =>
  Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.csGlob_intAdApprox F E (Fin n) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top g x

theorem isSDLat_globLat (hc : CMData F E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hx : x ∈ UAd hc n) :
    IsSDLat E n (Formalism.UG.CS.globLat x (stdLat E n)) := by
  have hlat := Formalism.UG.P.global_lattice_isLattice_holds F E (Fin n) (stdLat E n)
    (Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg) (stdLat_lattice (E := E) (n := n)).span_eq_top x
  have hU := globLat_unimodular hc n hx
  refine ⟨hlat.fg, hlat.span_eq_top, fun y => ?_⟩
  conv_lhs => rw [← hU]
  rw [mem_dual]
  refine forall₂_congr fun z _ => ?_
  rw [Submodule.mem_one, RingHom.mem_range]
  exact Iff.rfl

end Lat

section Rep

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)



end Rep

section Rel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

def RelReads (D : D7) {σ₀ : X.K →+* ℂ} (K : KerAmbTied D X σ₀) (Dc : DetChr X R.m) (hc : CMData X.F X.E) (u : Pr.Word) : Prop :=
  ∀ j (cl : StCl W Λ u j), ∃ y : D.Dt,
    ((D.chiD y : ℂˣ) : ℂ) = σ₀ ((Formalism.L2.DIV.detTw hc.sig Dc.chi (repPt W Λ hc u j cl) : X.Kˣ) : X.K) ∧
      ∃ L L' : SDLat D.host.E (R.N j), L.1 = StandardLatticesGL3.stdL D (R.N j) ∧ L'.1 = K.seam.lat (repN W Λ u j cl) ∧
        (QuotientGroup.mk y : D.Dt ⧸ D.UO) = D.relDet (R.N j) L L'



end Rel

end DetChrChi

end Formalism.L2.Col
end
end
