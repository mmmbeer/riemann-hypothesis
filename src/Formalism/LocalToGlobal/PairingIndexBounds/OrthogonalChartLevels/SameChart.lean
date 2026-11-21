import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.RecLev
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CembCL
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.KerTh
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.ClsSEqIffExistsLevCSmul
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteClassSetOfFiniteIndex
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.GramDetIsUnit
import Formalism.LocalToGlobal.HermitianColumns.ZeroPointScaledByCharacter
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosCompatOfBase
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepRec

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (hg : ∀ a, D.host.g a ≠ 0)
  (hpg : ∀ a, Nat.Coprime p (D.host.g a))
  (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
  (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ (D.mem u).A.T D.R.f (i + 1))
  (Ch : Chain (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k)
  (hfin : ∀ j c', ((levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx).lev j c').FinClasses)

variable (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))

include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in

def ptRec : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j →
    PtD D.host.F D.host.E (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
  | 0, La => ptStep0 (I := I) (isUnit_det_gram0 D.sp) (k_pred D.R) (repP Lc p) a bad La.1 La.2
  | i + 1, La => ptStep (((Sx i La.1.1 La.1.2.1).toStepAt hg hpg).toG (gram_herm D.sp.cm (D.sp.X (i + 1)))
      (gram_det_unit D.sp.cm (D.sp.X (i + 1))) (Sx i La.1.1 La.1.2.1).lev.U (Sx i La.1.1 La.1.2.1).lev.U_eq)
      (by exact rank_step D i La.1.1) a bad La.1.2.2 La.2

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1) → Formalism.L2.Col.HomE D.host.E
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)

include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in

def mRec : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → Fin (nOrb (zPsi D.R.toFrame h)) →
    Matrix (Fin (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)) (Fin (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)) (QQ p (orderOf (zPsi D.R.toFrame h)))
  | 0, _, v => frCoM (sp := D.sp) (I := I) D.sp.gram0 I.frS (k_pred D.R) v
  | i + 1, La, v => frCoM (sp := D.sp) (I := I) (D.sp.X (i + 1)).gram (Sx i La.1.1 La.1.2.1).fr (by exact rank_step D i La.1.1) v

include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in

def twC (v : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pl) (s : Fin ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).G.P.n' v)) : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).G.P.Qq v →+* ℂ_[p] :=
  letI := algKfC (cembCL D u h L h5 h2 he r Lc I ψ e).toCEmb
  tw (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin) ℂ_[p] v s

include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in
open Classical in

def subB (j : ℕ) (La : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j) (La' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1))
    (x y : D.what₂.Tau × Fin (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) × Fin (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)) : ℂ_[p] :=
  if x.1 = y.1 then
    (if IsOddPos ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm x.1).2 then
      ((mRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin j La
          ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm x.1).1).map
        (twC D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin _
          ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm x.1).2))
        x.2.2 y.2.2 *
      (((mRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin (j + 1) La'
          ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm x.1).1)⁻¹).map
        (twC D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin _
          ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm x.1).2))
        y.2.1 x.2.1
    else
      ((mRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin (j + 1) La'
          ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm x.1).1).map
        (twC D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin _
          ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm x.1).2))
        x.2.1 y.2.1 *
      (((mRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin j La
          ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm x.1).1)⁻¹).map
        (twC D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin _
          ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm x.1).2))
        y.2.2 x.2.2)
  else 0

variable {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g)

include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in

def Frec (j : ℕ) (La : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j)
    (La' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1)) :
    MvPowerSeries (D.what₂.Tau × Fin (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) ×
      Fin (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)) ℂ_[p] :=
  linSub (fun x y => ltC g hLT * subB D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin j La La' x y) <|
  ((p : ℂ_[p]) ^ (∑ v : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pl, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).vm v (j + 1) *
      (len (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin) v (j + 1) La'.2 - len (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin) v j La.2))) •
  serP lam fun z =>
    (muT (j + 1) (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad (j + 1) La').dt *
      (muT (j + 1) (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad j La).dt)⁻¹ *
      (Base.chiFac χ _ _ (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad j La).N
        (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad (j + 1) La').N)⁻¹ *
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad j La).N) ^ (-(((j * ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).t + 1) / 2 : ℕ) : ℤ))) *
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad (j + 1) La').N) ^ ((((j + 1) * ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).t + 1) / 2 : ℕ) : ℤ))) *
    kerTh B χ SS cl (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad j La).N
      (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad (j + 1) La').N
      (movD (Ξ₀ j La La') (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad j La).g
        (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad (j + 1) La').g) z

variable (hst : FinStab (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))

end Formalism.L2.PairingIndexBounds.F
end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (hg : ∀ a, D.host.g a ≠ 0)
  (hpg : ∀ a, Nat.Coprime p (D.host.g a))
  (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
  (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ (D.mem u).A.T D.R.f (i + 1))
  (Ch : Chain (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k)
  (hfin : ∀ j c', ((levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx).lev j c').FinClasses)

variable (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1) → Formalism.L2.Col.HomE D.host.E
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)

omit hp in

theorem unit_of_br {q : ℕ} [Fact q.Prime] (k : ℤ) (x : ℂ_[q]) (h : ‖x‖ = ‖(q : ℂ_[q])‖ ^ (-k)) : ‖(q : ℂ_[q]) ^ k * x‖ = 1 := by
  have hq0 : ‖(q : ℂ_[q])‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact_mod_cast (Fact.out : q.Prime).ne_zero
  rw [norm_mul, norm_zpow, h, zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hq0)]

include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in

def expF (j : ℕ) (La : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j) (La' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1)) : ℤ :=
  ∑ v : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pl, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).vm v (j + 1) * (len (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin) v (j + 1) La'.2 - len (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin) v j La.2)

include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in

def scalF (j : ℕ) (La : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j) (La' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1)) : ℂ :=
  muT (j + 1) (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad (j + 1) La').dt * (muT (j + 1) (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad j La).dt)⁻¹ *
    (Base.chiFac χ _ _ (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad j La).N (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad (j + 1) La').N)⁻¹ *
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad j La).N) ^ (-(((j * ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).t + 1) / 2 : ℕ) : ℤ))) *
      χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (ptRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad (j + 1) La').N) ^ ((((j + 1) * ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).t + 1) / 2 : ℕ) : ℤ))

include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in

def facF (j : ℕ) (La : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j) (La' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1)) : ℂ_[p] :=
  (p : ℂ_[p]) ^ (expF D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin j La La') *
    TaylorLogMetric.lamC lam (scalF D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad χ muT j La La')

include h5 h2 he r ψ e c hc Ch hr1 hr2 hfin in

def BRAt : Prop :=
  ∀ j (La : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j) (La' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1)), ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).IsLatTup La.2 → ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).IsLatTup La'.2 →
    ‖TaylorLogMetric.lamC lam (scalF D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a bad χ muT j La La')‖ =
      ‖(p : ℂ_[p])‖ ^ (-(expF D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin j La La'))

end Formalism.L2.PairingIndexBounds.F
end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.G.Cmp
open Formalism.L2.Col Formalism.HermitianLatticesTheory
open scoped TensorProduct

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [hp : Fact p.Prime] (D : D7) (u : D.what₂.Word) (h : D.R.MA)
  (L : IntermediateField (KO p (orderOf (zPsi D.R.toFrame h))) (Om p (orderOf (zPsi D.R.toFrame h))))
  [FiniteDimensional (KO p (orderOf (zPsi D.R.toFrame h))) L]
  (h5 : 5 ≤ p) (h2 : 2 ≤ orderOf (zPsi D.R.toFrame h)) (he : Even (orderOf (zPsi D.R.toFrame h))) (r : ℕ)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : LocId Lc p (nOrb (zPsi D.R.toFrame h)) (WQ p (orderOf (zPsi D.R.toFrame h))) (QQ p (orderOf (zPsi D.R.toFrame h))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ) (e : ℕ)
  (c : ℕ) (hc : CloudBound D u c)
  (hg : ∀ a, D.host.g a ≠ 0)
  (hpg : ∀ a, Nat.Coprime p (D.host.g a))
  (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
  (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I (OL p (orderOf (zPsi D.R.toFrame h)) L)ˣ (D.mem u).A.T D.R.f (i + 1))
  (Ch : Chain (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx))
  (hr1 : 1 ≤ r) (hr2 : 2 * r ≤ D.R.k)
  (hfin : ∀ j c', ((levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx).lev j c').FinClasses)

variable (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (lam : TaylorLogMetric.Qbar →+* ℂ_[p])
  (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
  (Ξ₀ : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1) → Formalism.L2.Col.HomE D.host.E
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1)
    (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) → ℂ)
  (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ)

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def OrthTie : Prop :=
  (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 co) ∧
    ∀ i, i < D.R.m → ∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram co

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def ATie : Prop :=
  compan (sp := D.sp) D.sp.gram0 a Lc.Lb = D.sp.crdLat0 (D.sp.X 0).L0 ∧
    ∀ (i : ℕ) (hi : i < D.R.m) (β : Cb i hi), compan (sp := D.sp) (D.sp.X (i + 1)).gram a (Sx i hi β).lev.Lb =
      Formalism.L2.Herm.crdLat (D.sp.X (i + 1)) (D.sp.X (i + 1)).L0

def MuTie (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ) : Prop :=
  ∀ j, muT j 1 = 1 ∧ (∀ x y, muT j (x * y) = muT j x * muT j y) ∧ ∀ x, muT j x ≠ 0 ∧ muT j x ∈ TaylorLogMetric.Qbar

def ChiTie (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  TaylorLogMetric.IsChi D χ ∧ ∀ 𝔞, χ 𝔞 ≠ 0 ∧ χ 𝔞 ∈ TaylorLogMetric.Qbar

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def baseComp : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → Submodule (𝓞 D.host.E) (Fin (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1) → D.host.E)
  | 0, _ => (compan (sp := D.sp) D.sp.gram0 a Lc.Lb).map
      (((reE (E := D.host.E) (n := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj 0).m + 1) (by exact (k_pred D.R).symm) : _ ≃ₗ[D.host.E] _) : _ →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))
  | i + 1, La => (compan (sp := D.sp) (D.sp.X (i + 1)).gram a (Sx i La.1.1 La.1.2.1).lev.Lb).map
      (((reE (E := D.host.E) (n := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (i + 1)).m + 1) (by exact (rank_step D i La.1.1).symm) : _ ≃ₗ[D.host.E] _) :
        _ →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def sameChart : ∀ j, (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j → Prop
  | 0, _, _ => True
  | _ + 1, La, Lb => La.1.2.1 = Lb.1.2.1

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def XiInv : Prop :=
  ∀ j (La : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j) (La' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1)) (x m : HomE D.host.E (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1) (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1)),
    (∀ P ∈ SS, ((cl : D.host.E)⁻¹ • m) ∈ localization₂ (W := HomE D.host.E (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1) (((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1)) P.asIdeal
      (homO (E := D.host.E) (a := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1) (b := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) (baseComp D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a j La)
        (baseComp D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a (j + 1) La'))) →
    Ξ₀ j La La' (x + m) = Ξ₀ j La La' x

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def XiLat : Prop :=
  ∀ j, j < D.R.m → ∀ (La : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j) (La' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1)),
    ∃ x ∈ homO (E := D.host.E) (a := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj j).m + 1) (b := ((sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Pj (j + 1)).m + 1) (baseComp D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a j La)
      (baseComp D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin a (j + 1) La'), Ξ₀ j La La' x ≠ 0

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def XiChart : Prop :=
  ∀ j (La Lb : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt j) (La' Lb' : (sysRec D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin).Lt (j + 1)),
    sameChart D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin j La Lb →
    sameChart D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin (j + 1) La' Lb' → Ξ₀ j La La' = Ξ₀ j Lb Lb'

include h5 h2 he r ψ e c hc hg hpg Ch hr1 hr2 hfin in

def LamPos : Prop :=
  ∀ (τ : D.what₂.Tau) (x : D.host.E) (hx : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar),
    lam ⟨TaylorLogMetric.embT D τ x, hx⟩ =
      twC D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx Ch hr1 hr2 hfin ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1 ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).2
        ((I.eQ ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1).symm
          (fstV I ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1 (inclE (F := D.host.F) (((I.plc ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).1)).adicCompletion D.host.F)
            (if IsOddPos ((posL D u h L h5 h2 he r Lc I ψ e c hc (levelsL D u h L h5 h2 he r Lc I ψ e c hc hg hpg Cb Sx) Ch hr1 hr2 hfin).symm τ).2 then D.host.conj x else x))))

end Formalism.L2.PairingIndexBounds.F
end
end
