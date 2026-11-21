import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
import Formalism.LocalToGlobal.KernelLattices.ColumnData.AmbOfENeSd
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Imports
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SplitPairOfGen
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.LocalToGlobal.KernelLattices.ColumnData.XiEquivD
import Formalism.LocalToGlobal.KernelLattices.ColumnData.XiEquivCOf

noncomputable section

open NumberField Formalism.BasicNotions

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.L2.Col Formalism.L2.GlobalTheoryTheory.Jets

section Bridge

variable (D : D7)










variable {D}

def KapChoice.toCar {γ₀ : IsoK D} (k : KapChoice γ₀) : Cd.KapChoice (D := Car.ofRec D) γ₀ where
  pp := k.pp
  pp_over := k.pp_over
  pi := k.pi
  pi_gen := k.pi_gen
  gaP := k.gaP
  gaP_at := k.gaP_at
  rt := k.rt
  rt_pow := k.rt_pow

def KapChoice.ofCar {γ₀ : IsoK D} (k : Cd.KapChoice (D := Car.ofRec D) γ₀) : KapChoice γ₀ where
  pp := k.pp
  pp_over := k.pp_over
  pi := k.pi
  pi_gen := k.pi_gen
  gaP := k.gaP
  gaP_at := k.gaP_at
  rt := k.rt
  rt_pow := k.rt_pow

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def Base.toCar (B : Base D cc δ) : Cd.Base (Car.ofRec D) cc δ where
  L := B.L
  lat := B.lat
  ω₀ := B.ω₀
  t0 := B.t0
  γ₀ := B.γ₀
  gC := B.gC
  gC_spec := B.gC_spec
  kc := B.kc.toCar

def Base.ofCar (B : Cd.Base (Car.ofRec D) cc δ) : Base D cc δ where
  L := B.L
  lat := B.lat
  ω₀ := B.ω₀
  t0 := B.t0
  γ₀ := B.γ₀
  gC := B.gC
  gC_spec := B.gC_spec
  kc := KapChoice.ofCar B.kc










variable {X : Fields}

def Seam.toCar (s : Seam D X) : Cd.Seam (Car.ofRec D) X := ⟨s.iE, s.iT, s.σ₀⟩

def Seam.ofCar (s : Cd.Seam (Car.ofRec D) X) : Seam D X := ⟨s.iE, s.iT, s.σ₀⟩




end Bridge

section OverColDat

variable (d : ColDat)



variable {d}

theorem AmbIn.ok_of (I : AmbIn d) (hχ : Cd.TaylorLogMetric.IsChi (carD d) I.χ) : I.Ok :=
  ⟨I.B.stdOK (Cd.isCurveIdeal_ccK (carD d)) I.ambient_isTwelfthRootDisc, hχ⟩



theorem repN_sd (u : d.Pr.Word) (i : ℕ) (c : StCl (Pr := d.Pr) d.W d.lev u i) : IsSdLat (repN (Pr := d.Pr) d.W d.lev u i c) :=
  ⟨((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.rep c).2.lat, ((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.rep c).2.uni⟩

set_option maxHeartbeats 1600000 in

theorem AmbIn.xiHyp (I : AmbIn d) (h : d.what₂.embLL.comp d.embE = d.host.φ₀) (hχ : Cd.TaylorLogMetric.IsChi (carD d) I.χ) (S : Set ℕ)
    (m0 : Fin d.R.m → Formalism.L2.Host.HChar d.X.E) {n m2 : ℕ} (hm : d.R.m = m2 + 2) (G : ChainGlob (Pr := d.Pr) d.W d.σ₀)
    (rat : ∀ u i, i < d.R.m → I.amb.JetsRat (d.R.N i) (d.R.N (i + 1)) (Sall (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) u)
      (cAof (selD d) _ (cstD d S m0 n) * cBof (selD d) _ (cstD d S m0 n) u))
    (rho : ∀ u, RhoScal (Pr := d.Pr) d.W d.lev d.Ch (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) G I.amb u) (u : d.Pr.Word) :
    XiHyp (Pr := d.Pr) d.W d.lev d.Ch (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) I.amb u
      (refXi1 d.Ch (selD d) (Formalism.L2.DIV.mu0 d.X.F d.X.E d.X.K S) (cstD d S m0 n) (idxD d S m2) (qe_one (selD d)) m2 (alD d S m2) u) G :=
  xiHypD d S m0 hm G I.amb rfl (fun i _ => I.eSmooth h i (i + 1)) rat
    (fun u i _ c c' => I.chiF_ne h hχ i (i + 1) (repN_sd u i c) (repN_sd u (i + 1) c')) rho u





def Car.ofColRec (c : ColRec) : Car := ⟨c.R, c.host, ⟨c.what₂.Tau, c.what₂.card_Tau⟩, c.eTau⟩


end OverColDat


namespace Test

open Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits

def exampleCMData : Car := ⟨R0, H0, ⟨R0.Psi, by rw [card_Psi]; rfl⟩, Equiv.refl _⟩


end Test

end Formalism.L2.Ker
