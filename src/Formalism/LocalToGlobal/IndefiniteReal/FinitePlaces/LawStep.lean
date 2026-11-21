import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SbHalfHalfInd
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FstACoordOfInfPart
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.VacExA
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceFinal
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatLevel
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsThetaFunOPull

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def LatPres {S T : HSp D} (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) : Prop :=
  ∀ (g : GA D S) (h : GA D T), g ∈ GfC S → h ∈ GfC T → Lev.finE S g ∈ Formalism.L2.DIV.St βS →
    Lev.finE T h ∈ Formalism.L2.DIV.St βT → ∀ t : WO S T, actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT

def VacFixOffO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    WeilFull.SphInertAtO ψ S T χS χT om → S.rank ≠ T.rank → (Even S.rank ∨ Even T.rank) →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
    Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → UnrOff e χS → UnrOff e χT →
    ∀ f₀ : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latAll S T ΛS ΛT) f₀ →
    (∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1) →
    ∀ (g : GA D S) (h : GA D T), g ∈ GfC S → h ∈ GfC T → Lev.finE S g ∈ Formalism.L2.DIV.St βS →
      Lev.finE T h ∈ Formalism.L2.DIV.St βT →
      (∀ i j, (e + cA D e) * (Formalism.L2.Theta.mt S g - 1) i j = 0) →
      (∀ i j, (e + cA D e) * (Formalism.L2.Theta.mt T h - 1) i j = 0) →
      om (g, h) f₀ = f₀

theorem placeIdem_sA (v : HeightOneSpectrum (𝓞 D.host.F)) : IsPlaceIdem D v (sA v (1 : v.adicCompletion D.host.F)) :=
  ⟨sglV v 1, rfl, by classical exact Pi.single_eq_same v (1 : v.adicCompletion D.host.F),
    fun v' hv' => by classical exact Pi.single_eq_of_ne hv' (1 : v.adicCompletion D.host.F)⟩

theorem resG_inv {V : HSp D} {ε : AF D.host.F} (hε : IsIdempotentElem ε) (g : GA D V) :
    (resG V ε g)⁻¹ = resG V ε g⁻¹ := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [← resG_mul (V := V) (ε := ε) hε, inv_mul_cancel, resG_one (V := V) (ε := ε) hε]

theorem mt_resG' {V : HSp D} {ε : AF D.host.F} (hε : IsIdempotentElem ε) (g : GA D V) :
    Formalism.L2.Theta.mt V (resG V ε g) = 1 + algebraMap (AF D.host.F) (AE D) ε • (Formalism.L2.Theta.mt V g - 1) := by
  rw [mt_resG (V := V) (ε := ε) hε]
  rfl

theorem mt_resG_sub {V : HSp D} {ε : AF D.host.F} (hε : IsIdempotentElem ε) (g : GA D V) (i j : Fin V.rank) :
    (Formalism.L2.Theta.mt V (resG V ε g) - 1) i j = algebraMap (AF D.host.F) (AE D) ε * (Formalism.L2.Theta.mt V g - 1) i j := by
  rw [mt_resG' hε, add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul]

theorem eps_orth {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : ∀ PP ∈ P, belowPl PP ≠ v) :
    (e + cA D e) * algebraMap (AF D.host.F) (AE D) (sA v 1) = 0 := by
  rw [he, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_eq_zero fun PP hPP => ?_
  have h1 : es PP * phiE (belowPl PP) 1 = es PP := idemAt_eps (hes PP hPP)
  have h2 : es PP + cA D (es PP) = phiE (D := D) (belowPl PP) 1 := below_of_idemAt (hes PP hPP)
  have h3 : phiE (D := D) (belowPl PP) 1 * phiE v 1 = 0 := phiE_orth (hv PP hPP)
  change (es PP + cA D (es PP)) * phiE v 1 = 0
  rw [h2, h3]

theorem eps_absorb {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP) (hc : e * cA D e = 0)
    {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ P) :
    algebraMap (AF D.host.F) (AE D) (sA (belowPl PP) 1) * (e + cA D e) =
      algebraMap (AF D.host.F) (AE D) (sA (belowPl PP) 1) := by
  have hsum : e + cA D e = ∑ Q ∈ P, phiE (D := D) (belowPl Q) 1 := by
    rw [he, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun Q hQ => below_of_idemAt (hes Q hQ)
  change phiE (D := D) (belowPl PP) 1 * (e + cA D e) = phiE (D := D) (belowPl PP) 1
  rw [hsum, Finset.mul_sum, Finset.sum_eq_single_of_mem PP hPP]
  · rw [← phiE_mul, one_mul]
  · intro Q hQ hne
    exact phiE_orth fun h => hne (idemSum_below_inj hes he hc hPP hQ h).symm

theorem unrAtV_of_unrOff {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : (e + cA D e) * algebraMap (AF D.host.F) (AE D) (sA v 1) = 0) {χ : (AE D)ˣ →* Circle} (hU : UnrOff e χ) :
    WeilFull.UnrAtV (sA v 1) χ := by
  intro x hx hf hfi
  set a := algebraMap (AF D.host.F) (AE D) (sA v 1) with ha
  have hx' : (x : AE D) - 1 = a * ((x : AE D) - 1) := by linear_combination hx
  have hinf : infPart D a = 0 := by
    have h0 : fstA D.host.F (sA v (1 : v.adicCompletion D.host.F)) = 0 := rfl
    rw [ha]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E))
      (sA v (1 : v.adicCompletion D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul, h0, TensorProduct.zero_tmul]
  have hinfx : infPart D (x : AE D) = 1 := by
    have h1 := congrArg (infPart D) hx'
    rw [map_sub, map_mul, hinf, zero_mul, map_one, sub_eq_zero] at h1
    exact h1
  have hex : (e + cA D e) * (x : AE D) = e + cA D e := by
    have h2 : (e + cA D e) * ((x : AE D) - 1) = 0 := by rw [hx', ← mul_assoc, hv, zero_mul]
    linear_combination h2
  exact hU x hinfx hf hfi hex

theorem algebraMap_AE_eq_zero {a : AF D.host.F} (h : algebraMap (AF D.host.F) (AE D) a = 0) : a = 0 := by
  have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F)
    (A := AF D.host.F) (B := D.host.E) (algebraMap D.host.F D.host.E).injective
  exact hinj (by rw [map_zero]; exact h)

theorem sA_one_ne_zero (v : HeightOneSpectrum (𝓞 D.host.F)) : sA v (1 : v.adicCompletion D.host.F) ≠ 0 := by
  intro h
  have h2 := congrArg (fun z => evalV D.host.F v (sndA D.host.F z)) h
  simp only [map_zero] at h2
  have h3 : evalV D.host.F v (sndA D.host.F (sA v (1 : v.adicCompletion D.host.F))) = 1 := by
    classical exact Pi.single_eq_same v (1 : v.adicCompletion D.host.F)
  exact one_ne_zero (h3.symm.trans h2)

theorem two_not_mem_of_inert {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hin : ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) (sA v 1) = 0) : (2 : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro h2
  obtain ⟨e, ε, hs, hε, hse⟩ := twoSplitIdem D v h2
  rw [placeIdem_eq hε] at hse
  have h0 := hin e hs
  rw [← hse] at h0
  have he0 : e = 0 := by
    have : e * (e + cA D e) = e := by rw [mul_add, hs.1, hs.2.1, add_zero]
    rw [← this, h0]
  rw [he0, map_zero, add_zero] at hse
  exact sA_one_ne_zero v (algebraMap_AE_eq_zero hse.symm)

set_option maxHeartbeats 1000000 in

theorem loc_fix (hSL : SplitLin D) (hPM : PlaceModelAt D) (hSOI : SplitOrInert D) {ψ : AddChar (AF D.host.F) ℂ}
    {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) (hI : WeilFull.SphInertAtO ψ S T χS χT om) (hrk : S.rank ≠ T.rank)
    (hev : Even S.rank ∨ Even T.rank)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hsS : IsSelfDualC S ΛS) (hsT : IsSelfDualC T ΛT) {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    (hfS : Formalism.L2.DIV.IsFrame βS ΛS) (hfT : Formalism.L2.DIV.IsFrame βT ΛT) (hLP : LatPres ΛS ΛT βS βT)
    {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (huS : UnrOff e χS) (huT : UnrOff e χT)
    {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀) (hlat : IsLatVac (heisO ψ S T) (latAll S T ΛS ΛT) f₀)
    (hn : ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1)
    {g : GA D S} {h : GA D T} (hgf : g ∈ GfC S) (hhf : h ∈ GfC T) (hgS : Lev.finE S g ∈ Formalism.L2.DIV.St βS)
    (hhT : Lev.finE T h ∈ Formalism.L2.DIV.St βT)
    (hgP : ∀ i j, (e + cA D e) * (Formalism.L2.Theta.mt S g - 1) i j = 0)
    (hhP : ∀ i j, (e + cA D e) * (Formalism.L2.Theta.mt T h - 1) i j = 0) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    om (resG S (sA v 1) g, resG T (sA v 1) h) f₀ = f₀ := by
  have hε : IsIdempotentElem (sA v (1 : v.adicCompletion D.host.F)) := sA_idem v
  obtain ⟨⟨es, hes, hesum⟩, hc⟩ := he
  set s := algebraMap (AF D.host.F) (AE D) (sA v 1) with hsdef
  have hgv : Lev.finE S (resG S (sA v 1) g) ∈ Formalism.L2.DIV.St βS := finE_resG_mem_St (V := S) hε hgS
  have hhv : Lev.finE T (resG T (sA v 1) h) ∈ Formalism.L2.DIV.St βT := finE_resG_mem_St (V := T) hε hhT
  by_cases hunder : ∃ PP ∈ P, belowPl PP = v
  ·
    obtain ⟨PP, hPP, rfl⟩ := hunder
    have hab := eps_absorb hes hesum hc hPP
    have hg1 : resG S (sA (belowPl PP) 1) g = 1 := by
      apply gaExt
      rw [mtG_one]
      ext i j
      have := mt_resG_sub (V := S) hε g i j
      rw [← hab, mul_assoc, hgP i j, mul_zero] at this
      simpa [sub_eq_zero] using this
    have hh1 : resG T (sA (belowPl PP) 1) h = 1 := by
      apply gaExt
      rw [mtG_one]
      ext i j
      have := mt_resG_sub (V := T) hε h i j
      rw [← hab, mul_assoc, hhP i j, mul_zero] at this
      simpa [sub_eq_zero] using this
    rw [hg1, hh1, ← Prod.one_eq_mk, map_one, Module.End.one_apply]
  · push Not at hunder
    have horth := eps_orth hes hesum hunder
    rcases hSOI v _ (placeIdem_sA v) with ⟨PP, hPPv, hPPc⟩ | hin
    ·
      obtain ⟨e', he', ε', hε', hse'⟩ := idem_at PP hPPc v hPPv
      rw [placeIdem_eq hε'] at hse'
      have hsp : IsSplitIdem D e' := he'.1
      have hsum1 : IsIdemSum e' {PP} := ⟨⟨fun _ => e', by simpa using he', by simp⟩, hsp.2.1⟩
      have horth' : (e + cA D e) * e' = 0 := by
        have : e' = e' * (e' + cA D e') := by rw [mul_add, hsp.1, hsp.2.1, add_zero]
        rw [this, hse', mul_comm e', ← mul_assoc, horth, zero_mul]
      have hfac : splitFacO χS χT (detAt e' S (resG S (sA v 1) g)) (detAt e' T (resG T (sA v 1) h)) = 1 := by
        simp only [splitFacO, unrOff_detAt he' horth' S hgv huT, unrOff_detAt he' horth' T hhv huS, inv_one, mul_one]
      have hgvi : Lev.finE S (resG S (sA v 1) g)⁻¹ ∈ Formalism.L2.DIV.St βS := by
        rw [map_inv]; exact inv_mem hgv
      have hhvi : Lev.finE T (resG T (sA v 1) h)⁻¹ ∈ Formalism.L2.DIV.St βT := by
        rw [map_inv]; exact inv_mem hhv
      exact fix_split hSL hPM hW hsS hsT he' hf₀ hlat hn (suppAt_resG (V := S) hε g hse') (suppAt_resG (V := T) hε h hse')
        (isDetAt_detAt hsp.1 S _) (isDetAt_detAt hsp.1 T _) hfac
        (fun t _ => hLP _ _ (resG_mem_GfC (V := S) hε hgf) (resG_mem_GfC (V := T) hε hhf) hgv hhv t)
        (fun t _ => hLP _ _ (inv_mem (resG_mem_GfC (V := S) hε hgf)) (inv_mem (resG_mem_GfC (V := T) hε hhf)) hgvi hhvi t)
    ·
      have hsupp : ∀ (V : HSp D) (x : GA D V), WeilFull.SuppV (sA v 1) V (resG V (sA v 1) x) := by
        intro V x i j
        rw [mt_resG_sub (V := V) hε x i j, ← mul_assoc, algIdem hε]
      exact fix_inert hI hrk hev hsS hsT hfS hfT (placeIdem_sA v) (two_not_mem_of_inert hin) hin
        (unrAtV_of_unrOff horth huS) (unrAtV_of_unrOff horth huT) (hsupp S g) (hsupp T h) hgv hhv hf₀ hlat

theorem vacFixOff_of (hSL : SplitLin D) (hPM : PlaceModelAt D) (hSOI : SplitOrInert D)
    (hLP : ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
      (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
      (βT : GL (Fin T.rank) (Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS →
        Formalism.L2.DIV.IsFrame βT ΛT → LatPres ΛS ΛT βS βT) :
    VacFixOffO D := by
  intro ψ S T χS χT om hW hI hrk hev ΛS ΛT hsS hsT βS βT hfS hfT P e he huS huT f₀ hf₀ hlat hn g h hgf hhf hgS hhT
    hgP hhP
  have hLP' := hLP S T ΛS ΛT βS βT hsS hsT hfS hfT
  refine om_fix_of_trunc hW hf₀ hgf hhf (fun A => resG S (idemS A) g) (fun A => resG T (idemS A) h)
    (fun A => mt_resG' (idemS_idem A) g) (fun A => by rw [resG_inv (idemS_idem A)]; exact mt_resG' (idemS_idem A) g⁻¹)
    (fun A => mt_resG' (idemS_idem A) h) (fun A => by rw [resG_inv (idemS_idem A)]; exact mt_resG' (idemS_idem A) h⁻¹)
    (fun A => ?_)
  classical
  induction A using Finset.induction_on with
  | empty =>
    simp only [idemS_empty, resG_zero_eps (V := S), resG_zero_eps (V := T)]
    rw [← Prod.one_eq_mk, map_one, Module.End.one_apply]
  | insert v A hv ih =>
    have hmul : idemS (insert v A) = sA v 1 + idemS A := by rw [idemS_insert hv, add_comm]
    have horth : sA v (1 : v.adicCompletion D.host.F) * idemS A = 0 := by rw [mul_comm]; exact idemS_mul_sA hv
    simp only [hmul]
    rw [← resG_orth (V := S) (sA_idem v) (idemS_idem A) horth g, ← resG_orth (V := T) (sA_idem v) (idemS_idem A) horth h,
      ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih]
    exact loc_fix hSL hPM hSOI hW hI hrk hev hsS hsT hfS hfT hLP' he huS huT hf₀ hlat hn hgf hhf hgS hhT hgP hhP v

end Formalism.IndefR.Fin.LevelGroupLemmas

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Matrix NumberField IsDedekindDomain
open Formalism.IndefR.Datum (LowZero topL omegaG omegaQ omegaK)

namespace Formalism.IndefR.Fin.LevelGroupLemmas

section Mat
variable {κ : Type} [CommRing κ]

end Mat

section GlobalTheory
variable {κ : Type} [CommRing κ]

end GlobalTheory

section Omega
variable {D : D7}

end Omega

section Conj
variable {D : D7}

end Conj

section Q
variable {D : D7}

end Q

section Det
variable {κ : Type} [CommRing κ]

end Det

section Lev
open scoped TensorProduct
variable {D : D7}

end Lev

section Laws
variable {D : D7}

end Laws

section Bridge
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

end Bridge

end Formalism.IndefR.Fin.LevelGroupLemmas

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

set_option maxHeartbeats 800000 in
theorem splitOrInert (D : D7) : LevelGroupLemmas.SplitOrInert D := by
  intro v ε hε
  by_cases h : ∃ e : AE D, IsSplitIdem D e ∧ e * algebraMap (AF D.host.F) (AE D) ε ≠ 0
  · left
    obtain ⟨e, ⟨h1, h2, w, ε', hpl, hs⟩, hne⟩ := h
    rw [placeIdem_eq hpl] at hs
    change e + cA D e = phiE w 1 at hs
    rw [placeIdem_eq hε] at hne
    change e * phiE v 1 ≠ 0 at hne
    have heps : e * phiE w 1 = e := by rw [← hs, mul_add, h1, h2, add_zero]
    have hwv : w = v := by
      by_contra hwv
      apply hne
      rw [← heps, mul_assoc, phiE_orth hwv, mul_zero]
    subst hwv
    obtain ⟨s, ι, hss, hι⟩ := split_emb h1 h2 hs
    refine ⟨plOf ι, ?_, plOf_split ι s hss hι⟩
    have hle : w.asIdeal ≤ (belowPl (plOf ι)).asIdeal := fun f hf => algebraMap_mem_valIdeal ι hf
    exact (w.isMaximal.eq_of_le (belowPl (plOf ι)).isPrime.ne_top hle).symm
  · right
    intro e he
    by_contra hne
    exact h ⟨e, he, hne⟩

end Formalism.IndefR.Fin

end
end

section
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (S T : HSp D)

theorem half_sub_of {e e₁ : AE D} (h : e₁ * e = e₁) {x : WO S T} (hx : IsHalf e₁ x) : IsHalf e x := fun i j => by
  rw [← hx i j, ← mul_assoc, mul_comm e e₁, h]

theorem chalf_sub_of {e e₁ : AE D} (h : e₁ * e = e₁) {y : WO S T} (hy : IsHalf (cA D e₁) y) :
    IsHalf (cA D e) y := fun i j => by
  rw [← hy i j, ← mul_assoc, ← map_mul, mul_comm e e₁, h]

theorem symplO_left_e₁ {e₁ : AE D} {t y : WO S T} (hy : IsHalf (cA D e₁) y) :
    symplO S T t y = symplO S T (t.map (fun a => e₁ * a)) y := by
  have hc : ∀ c b, cA D (y c b) = e₁ * cA D (y c b) := fun c b => by
    conv_lhs => rw [← hy c b]
    rw [map_mul, cA_cA]
  have e1 : hO S T t y = hO S T (t.map (fun a => e₁ * a)) y := by
    unfold hO
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.map_apply]
    conv_lhs => rw [hc c b]
    ring
  unfold symplO
  rw [e1]

theorem symplO_right_ce₁ {e₁ : AE D} {x y : WO S T} (hx : IsHalf e₁ x) :
    symplO S T x y = symplO S T x (y.map (fun a => cA D e₁ * a)) := by
  have e1 : hO S T x y = hO S T x (y.map (fun a => cA D e₁ * a)) := by
    unfold hO
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.map_apply, map_mul, cA_cA]
    conv_lhs => rw [← hx d a]
    ring
  unfold symplO
  rw [e1]

theorem symplO_nsmul_right (t y : WO S T) (k : ℕ) : symplO S T t (k • y) = symplO S T (k • t) y := by
  induction k with
  | zero => rw [zero_smul, zero_smul, symplO_zero_right, symplO_zero_left]
  | succ n ih => rw [succ_nsmul, succ_nsmul, symplO_add_right, symplO_add_left, ih]

set_option maxHeartbeats 800000 in

theorem actO_fix {e e₁ : AE D} (he : e * cA D e = 0) (h1 : e₁ * e = e₁) {g : GA D S} {h : GA D T}
    (hg : SuppAt e₁ S g) (hh : SuppAt e₁ T h) {t : WO S T} (ht : IsHalf e t) (h0 : ∀ i j, e₁ * t i j = 0) :
    actO S T g h t = t := by
  have hce : cA D e₁ * e = 0 := by
    have : cA D e₁ = cA D e₁ * cA D e := by rw [← map_mul, h1]
    rw [this, mul_assoc, mul_comm (cA D e) e, he, mul_zero]
  have hz : ∀ i j, (e₁ + cA D e₁) * t i j = 0 := fun i j => by
    rw [add_mul, h0 i j, zero_add, ← ht i j, ← mul_assoc, hce, zero_mul]
  have hL : HMul.hMul (mt T h) (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = t := by
    ext i j
    have h2 : ∀ k, ((mt T h) - 1) i k * t k j = 0 := fun k => by
      rw [← hh i k, mul_comm (e₁ + cA D e₁), mul_assoc, hz k j, mul_zero]
    have h3 : ∑ k, ((mt T h) - 1) i k * t k j = 0 := Finset.sum_eq_zero fun k _ => h2 k
    simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h3
    rw [Matrix.mul_apply]
    exact sub_eq_zero.1 h3
  have hR : HMul.hMul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g) = t := by
    ext i j
    have h2 : ∀ k, t i k * ((mt S g) - 1) k j = 0 := fun k => by
      rw [← hg k j, ← mul_assoc, mul_comm (t i k), hz i k, zero_mul]
    have h3 : ∑ k, t i k * ((mt S g) - 1) k j = 0 := Finset.sum_eq_zero fun k _ => h2 k
    simp only [Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3
    rw [Matrix.mul_apply]
    exact sub_eq_zero.1 h3
  have hinv : HMul.hMul (mt S g) (mt S g⁻¹) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    rw [← Formalism.IndefR.Eqv.mt_mul, mul_inv_cancel, Formalism.IndefR.Eqv.mt_one]
  have hR' : HMul.hMul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S g⁻¹) = t := by
    conv_lhs => rw [← hR]
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  unfold actO
  rw [hL, hR']

set_option maxHeartbeats 1600000 in

theorem evalYZero_zero (ψ : AddChar (AF D.host.F) ℂ) {e e₁ : AE D} (he₁ : IsSplitIdem D e₁) (h1 : e₁ * e = e₁)
    (Λ : AddSubgroup (WO S T))
    (hΛe₁ : ∀ u ∈ Λ, u.map (fun a => e₁ * a) ∈ Λ)
    (hLL₁ : ∀ x ∈ Λ, IsHalf e₁ x → ∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1)
    (hdX₁ : ∀ x, IsHalf e₁ x → (∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1) → x ∈ Λ)
    (hfY₁ : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf (cA D e₁) v ∧ u = r + k • v)
    (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hmo : ∀ Φ, IsSBHalf e Λ Φ → ∀ y, IsHalf (cA D e) y →
      Tm (fun t => ψ (symplO S T t y) * Φ t) = heisO ψ S T y (Tm Φ))
    (hth : ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ))
    (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ)
    (hℓ : ∀ u : WO S T, (∀ i j, cA D e₁ * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f)
    {Ψ : WO S T → ℂ} (hΨ : IsSBHalf e Λ Ψ) (hΨ0 : ∀ t, IsHalf e t → (∀ i j, e₁ * t i j = 0) → Ψ t = 0) :
    ℓ (Tm Ψ) = 0 := by
  classical
  have mi := fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h
  obtain ⟨hs, k, hk, hi, hl⟩ := hΨ
  have hK : 0 < k * k := Nat.mul_pos hk hk
  have hfinY : ∀ j, 0 < j → Finite (Four.Qt j (Λ ⊓ halfSub S T (cA D e₁))) := fun j hj => by
    obtain ⟨R, hR⟩ := hfY₁ j hj
    exact finite_qt_of S T R fun u hu => by
      obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
      exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩
  have htf : ∀ j : ℕ, 0 < j → ∀ t : WO S T, j • t = 0 → t = 0 := fun j hj t h => nsmul_eq_zero_WO S T hj h
  haveI := Four.Gk_finite hfinY htf hK
  letI := Fintype.ofFinite (Four.Gk Λ (halfSub S T (cA D e₁)) (k * k))
  let G := Four.Gk Λ (halfSub S T (cA D e₁)) (k * k)
  have hgY : ∀ g : G, IsHalf (cA D e₁) (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out)) := fun g i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, (Four.Gk_out g).1 i j]
  have he₁e₁ : ∀ a : AE D, e₁ * (e₁ * a) = e₁ * a := fun a => by rw [← mul_assoc, he₁.1]

  have hA : ∀ t, ∑ g : G, ψ (symplO S T t (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out))) * Ψ t = 0 := by
    intro t
    by_cases hΨt : Ψ t = 0
    · simp [hΨt]
    have ht := hs t hΨt
    have hkt := hl t hΨt
    set s : WO S T := (k • t).map (fun a => e₁ * a) with hsdef
    have hsΛ : s ∈ Λ := hΛe₁ _ hkt
    have hsh : IsHalf e₁ s := fun i j => by simp only [hsdef, Matrix.map_apply]; exact he₁e₁ _
    have hterm : ∀ g : G, ψ (symplO S T t (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out))) =
        ψ (symplO S T s ((g : Four.QY Λ (halfSub S T (cA D e₁))).out)) := by
      intro g
      rw [symplO_left_e₁ S T (hgY g), symplO_nsmul_right]
      congr 2
      ext i j
      simp only [hsdef, Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul]
      ring
    rw [← Finset.sum_mul, Finset.sum_congr rfl fun g _ => hterm g]
    have hcs := Four.chi_sum (χ := fun t y => ψ (symplO S T t y)) (L := Λ) (X := halfSub S T e₁)
      (Y := halfSub S T (cA D e₁))
      (fun t t' y => by simp only [symplO_add_left, AddChar.map_add_eq_mul])
      (fun t y y' => by simp only [symplO_add_right, AddChar.map_add_eq_mul])
      (fun t y => psi_ne_zero ψ _)
      (fun x hx y hy => hLL₁ x (mi hx).1 (mi hx).2 y (mi hy).1 (mi hy).2)
      (fun x hx h => hdX₁ x hx fun y hy hye => h y (AddSubgroup.mem_inf.2 ⟨hy, hye⟩))
      (fun j hj s' hs' => by obtain ⟨t', ht', h'⟩ := half_div S T hj hs'; exact ⟨t', ht', h'⟩)
      (fun j hj s' hs' => by obtain ⟨t', ht', h'⟩ := half_div S T hj hs'; exact ⟨t', ht', h'⟩)
      hfinY htf hK (AddSubgroup.mem_inf.2 ⟨hsΛ, hsh⟩)
    rw [finsum_eq_sum_of_fintype] at hcs
    rw [hcs]
    split_ifs with hin
    · exfalso
      obtain ⟨u, hu, hus⟩ := Four.mem_smulSub.1 hin
      have hu' := mi hu
      have he1t : t.map (fun a => e₁ * a) = k • u := by
        refine sub_eq_zero.1 (htf k hk _ ?_)
        rw [smul_sub, smul_smul, hus, sub_eq_zero, hsdef]
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul]
        ring
      have hdec : t = (t - t.map (fun a => e₁ * a)) + k • u := by rw [he1t, sub_add_cancel]
      apply hΨt
      rw [hdec, hi u hu'.1 (half_sub_of S T h1 hu'.2)]
      refine hΨ0 _ (fun i j => ?_) (fun i j => ?_)
      · rw [Matrix.sub_apply, Matrix.map_apply, mul_sub, ht i j, ← mul_assoc, mul_comm e e₁, h1]
      · rw [Matrix.sub_apply, Matrix.map_apply, mul_sub, he₁e₁, sub_self]
    · exact zero_mul _

  have hM : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfun : Ψ = (Fintype.card G : ℂ)⁻¹ • ∑ g : G,
      (Ψ - fun t => ψ (symplO S T t (k • ((g : Four.QY Λ (halfSub S T (cA D e₁))).out))) * Ψ t) := by
    funext t
    rw [Pi.smul_apply, Finset.sum_apply]
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hA t, sub_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul,
      inv_mul_cancel_left₀ hM]
  conv_lhs => rw [hfun]
  rw [map_smul, map_sum, map_smul, map_sum]
  refine (smul_eq_zero.2 (Or.inr (Finset.sum_eq_zero fun g _ => ?_)))
  rw [map_sub, map_sub, hmo Ψ ⟨hs, k, hk, hi, hl⟩ _ (chalf_sub_of S T h1 (hgY g)),
    hℓ _ (hgY g) _ (hth Ψ ⟨hs, k, hk, hi, hl⟩), sub_self]

end Formalism.IndefR.Fin

end
end

section
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (S T : HSp D)

theorem suppAt_inv_fp {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  have hinv : HMul.hMul (mt V g⁻¹) (mt V g) = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    rw [← Formalism.IndefR.Eqv.mt_mul, inv_mul_cancel, Formalism.IndefR.Eqv.mt_one]
  have hd : (mt V g⁻¹ : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1 =
      -(HMul.hMul (mt V g⁻¹) ((mt V g : Matrix (Fin V.rank) (Fin V.rank) (AE D)) - 1)) := by
    rw [Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub]
  intro i j
  rw [hd, Matrix.neg_apply, mul_neg, Matrix.mul_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hg k j]

theorem actO_nsmul (g : GA D S) (h : GA D T) (k : ℕ) (t : WO S T) : actO S T g h (k • t) = k • actO S T g h t := by
  induction k with
  | zero =>
    rw [zero_smul, zero_smul]
    unfold actO
    rw [Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, Formalism.IndefR.Eqv.actO_add, ih]

theorem isHalf_actO_fp {e : AE D} (g : GA D S) (h : GA D T) {t : WO S T} (ht : IsHalf e t) :
    IsHalf e (actO S T g h t) := by
  intro i j
  unfold actO
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← ht l k]
  ring

theorem isHalf_nsmul_fp {e : AE D} {v : WO S T} (hv : IsHalf e v) (m : ℕ) : IsHalf e (m • v) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hv i j]

theorem isHalf_actO_iff {e : AE D} (g : GA D S) (h : GA D T) (t : WO S T) :
    IsHalf e (actO S T g h t) ↔ IsHalf e t := by
  refine ⟨fun h' => ?_, isHalf_actO_fp S T g h⟩
  have := isHalf_actO_fp S T g⁻¹ h⁻¹ h'
  rwa [Formalism.IndefR.Eqv.actO_actO_inv] at this

open Classical in
theorem halfInd_add {e : AE D} {Λ : AddSubgroup (WO S T)} {u : WO S T} (hu : u ∈ Λ) (hue : IsHalf e u)
    (s : WO S T) : halfInd e Λ (s + u) = halfInd e Λ s := by
  unfold halfInd
  have h1 : s + u ∈ Λ ↔ s ∈ Λ := ⟨fun h => by simpa using Λ.sub_mem h hu, fun h => Λ.add_mem h hu⟩
  have h2 : IsHalf e (s + u) ↔ IsHalf e s := by
    constructor
    · intro h i j
      have := h i j
      rw [Matrix.add_apply, mul_add, hue i j] at this
      exact add_right_cancel this
    · intro h i j
      rw [Matrix.add_apply, mul_add, h i j, hue i j]
  simp only [h1, h2]

theorem sb_comp {e : AE D} {Λ : AddSubgroup (WO S T)} (g : GA D S) (h : GA D T)
    {k₁ : ℕ} (hk₁ : 0 < k₁) (h₁ : ∀ t ∈ Λ, k₁ • actO S T g h t ∈ Λ)
    {k₂ : ℕ} (hk₂ : 0 < k₂) (h₂ : ∀ t ∈ Λ, k₂ • actO S T g⁻¹ h⁻¹ t ∈ Λ)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) : IsSBHalf e Λ (fun t => Φ (actO S T g h t)) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := hΦ
  refine ⟨fun t ht => (isHalf_actO_iff S T g h t).1 (hs _ ht), k * k₁ * k₂, by positivity,
    fun u hu hue t => ?_, fun t ht => ?_⟩
  · show Φ (actO S T g h (t + (k * k₁ * k₂) • u)) = Φ (actO S T g h t)
    rw [Formalism.IndefR.Eqv.actO_add, actO_nsmul, show (k * k₁ * k₂) • actO S T g h u =
      k • (k₂ • (k₁ • actO S T g h u)) by rw [smul_smul, smul_smul]; ring_nf]
    exact hi _ (Λ.nsmul_mem (h₁ u hu) k₂)
      (isHalf_nsmul_fp S T (isHalf_nsmul_fp S T (isHalf_actO_fp S T g h hue) k₁) k₂) _
  · have h1 := hl _ ht
    have h2 := h₂ _ h1
    rw [actO_nsmul, Formalism.IndefR.Eqv.actO_actO_inv, smul_smul] at h2
    rw [show k * k₁ * k₂ = k₁ * (k₂ * k) by ring, ← smul_smul]
    exact Λ.nsmul_mem h2 k₁

end Formalism.IndefR.Fin

end
end

section
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix MeasureTheory NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem facts_at_e₁ (hPD : PlaceLatDual D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e e₁ : AE D}
    (he : IsIdemSum e P) (he₁ : IsSplitIdem D e₁) (h1 : e₁ * e = e₁) :
    (∀ u ∈ latAll S T ΛS ΛT, u.map (fun a => e₁ * a) ∈ latAll S T ΛS ΛT) ∧
    (∀ x ∈ latAll S T ΛS ΛT, IsHalf e₁ x → ∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1) ∧
    (∀ y, IsHalf (cA D e₁) y → (∀ x ∈ latAll S T ΛS ΛT, IsHalf e₁ x → ψ (symplO S T x y) = 1) →
      y ∈ latAll S T ΛS ΛT) ∧
    (∀ x, IsHalf e₁ x → (∀ y ∈ latAll S T ΛS ΛT, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1) →
      x ∈ latAll S T ΛS ΛT) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf e₁ v ∧ u = r + k • v) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf (cA D e₁) v ∧ u = r + k • v) ∧
    (∀ x, IsHalf e₁ x → ∃ k : ℕ, 0 < k ∧ k • x ∈ latAll S T ΛS ΛT) ∧
    (∀ y, IsHalf (cA D e₁) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ latAll S T ΛS ΛT) := by
  classical
  obtain ⟨hi, -, hP⟩ := hPD ψ hψ S T ΛS ΛT hS hT
  obtain ⟨hd2, hd3, hfin, hop⟩ := hP P e he
  have hc₁ := isSplitIdem_cA he₁
  have hmapH : ∀ (f : AE D), f * f = f → ∀ u : WO S T, IsHalf f (u.map (fun a => f * a)) := fun f hf u i j => by
    simp only [Matrix.map_apply]; rw [← mul_assoc, hf]
  have hmapId : ∀ (f : AE D) (u : WO S T), IsHalf f u → u.map (fun a => f * a) = u := fun f u hu => by
    ext i j; exact hu i j
  have hfinE : ∀ (f f' : AE D), f' * f' = f' → (∀ u : WO S T, IsHalf f' u → IsHalf f u) →
      (∀ u ∈ latAll S T ΛS ΛT, u.map (fun a => f' * a) ∈ latAll S T ΛS ΛT) →
      (∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf f u →
        ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf f v ∧ u = r + k • v) →
      ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ latAll S T ΛS ΛT, IsHalf f' u →
        ∃ r ∈ R, ∃ v ∈ latAll S T ΛS ΛT, IsHalf f' v ∧ u = r + k • v := by
    intro f f' hf' hsub hmul hF k hk
    obtain ⟨R, hR⟩ := hF k hk
    refine ⟨R.image (fun r => r.map (fun a => f' * a)), fun u hu hue => ?_⟩
    obtain ⟨r, hr, v, hv, -, huv⟩ := hR u hu (hsub u hue)
    refine ⟨r.map (fun a => f' * a), Finset.mem_image_of_mem _ hr, v.map (fun a => f' * a), hmul v hv,
      hmapH f' hf' v, ?_⟩
    rw [← hmapId f' u hue, huv]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
    ring
  refine ⟨fun u hu => hi e₁ he₁ u hu, fun x hx hxe y hy hye => (hd2 y (chalf_sub_of S T h1 hye)).2 hy x hx
    (half_sub_of S T h1 hxe), fun y hye H => (hd2 y (chalf_sub_of S T h1 hye)).1 fun x hx _ => ?_,
    fun x hxe H => (hd3 x (half_sub_of S T h1 hxe)).1 fun y hy _ => ?_,
    hfinE e e₁ he₁.1 (fun u hu => half_sub_of S T h1 hu) (hi e₁ he₁) (fun k hk => hfin k hk e (Or.inl rfl)),
    hfinE (cA D e) (cA D e₁) hc₁.1 (fun u hu => chalf_sub_of S T h1 hu) (hi (cA D e₁) hc₁)
      (fun k hk => hfin k hk (cA D e) (Or.inr rfl)),
    fun x hx => hop e (Or.inl rfl) x (half_sub_of S T h1 hx),
    fun y hy => hop (cA D e) (Or.inr rfl) y (chalf_sub_of S T h1 hy)⟩
  · rw [symplO_left_e₁ S T hye]
    exact H _ (hi e₁ he₁ x hx) (hmapH e₁ he₁.1 x)
  · rw [symplO_right_ce₁ S T hxe]
    exact H _ (hi (cA D e₁) hc₁ y hy) (hmapH (cA D e₁) hc₁.1 y)

open Classical in

theorem splitLin_of (hPD : PlaceLatDual D) (hlev : LatLevel D) : SplitLin D := by
  intro ψ S T χS χT om hω ΛS ΛT hS hT P e he f₀ hf₀ hvac Tm hTm e₁ he₁ h1 g h hg hh x y hx hy
  have hψ := hω.std
  obtain ⟨hΛe₁, hLL₁, hdY₁, hdX₁, hfX₁, hfY₁, -, hoY₁⟩ := facts_at_e₁ hPD hψ S T hS hT he he₁ h1
  obtain ⟨-, hvi, hP⟩ := hPD ψ hψ S T ΛS ΛT hS hT
  obtain ⟨hd2, -, -, -⟩ := hP P e he
  obtain ⟨Tc, -, huniq, htheta, -⟩ :=
    placeModelAt_of hPD ψ hψ S T ΛS ΛT hS hT P e he f₀ hf₀ hvac e (Or.inl rfl)
  have hthm : ∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsThetaFunO ψ S T (Tm Φ) := fun Φ hΦ => by
    rw [huniq Tm hTm Φ hΦ]; exact htheta Φ hΦ
  obtain ⟨r, hr, hsplit⟩ := hω.om_split e₁ he₁ g h hg hh x y hx hy
  set c : ℂ := (r : ℂ) * (splitFacO χS χT x y : ℂ) with hcdef
  have hc0 : c ≠ 0 := mul_ne_zero (by exact_mod_cast hr.ne') (Circle.coe_ne_zero _)
  obtain ⟨k₁, hk₁, h₁⟩ := hvi e₁ he₁ g h hg hh
  obtain ⟨k₂, hk₂, h₂⟩ := hvi e₁ he₁ g⁻¹ h⁻¹ (suppAt_inv_fp hg) (suppAt_inv_fp hh)
  have h₁' : ∀ t ∈ latAll S T ΛS ΛT, k₁ • actO S T g⁻¹⁻¹ h⁻¹⁻¹ t ∈ latAll S T ΛS ΛT := by
    simpa only [inv_inv] using h₁
  have hSBp : ∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ →
      IsSBHalf e (latAll S T ΛS ΛT) (fun t => Φ (actO S T g h t)) :=
    fun Φ hΦ => sb_comp S T g h hk₁ h₁ hk₂ h₂ hΦ
  have hSBq : ∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ →
      IsSBHalf e (latAll S T ΛS ΛT) (fun t => Φ (actO S T g⁻¹ h⁻¹ t)) :=
    fun Φ hΦ => sb_comp S T g⁻¹ h⁻¹ hk₂ h₂ hk₁ h₁' hΦ
  have hindSB : IsSBHalf e (latAll S T ΛS ΛT) (halfInd e (latAll S T ΛS ΛT)) :=
    (isSBHalf_iff S T).2 Four.isSB_ind
  have hf₀T : Tm (halfInd e (latAll S T ΛS ΛT)) = f₀ := by
    have := hTm.vac
    rwa [one_smul] at this

  have hG := hSBp _ hindSB
  have hG₁ := hthm _ hG
  have hw : om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) = c • f₀ := by
    by_contra hne
    have hw0 : om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) - c • f₀ ≠ 0 :=
      sub_ne_zero.2 hne
    have hwθ : IsThetaFunO ψ S T (om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) -
        c • f₀) := by
      rw [sub_eq_add_neg, ← neg_smul]
      exact Formalism.IndefR.Eqv.thetaO_add (hω.om_pres _ _ hG₁) (Formalism.IndefR.Eqv.thetaO_smul _ hf₀)

    have hfixG : ∀ u ∈ latAll S T ΛS ΛT, (IsHalf e₁ u ∨ IsHalf (cA D e₁) u) →
        heisO ψ S T (actO S T g⁻¹ h⁻¹ u) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) =
          Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t)) := by
      intro u hu hue
      rcases hue with hue | hue
      · have hqu : IsHalf e (actO S T g⁻¹ h⁻¹ u) := isHalf_actO_fp S T _ _ (half_sub_of S T h1 hue)
        rw [← hTm.trans _ hG _ hqu]
        congr 1
        funext t
        rw [Formalism.IndefR.Eqv.actO_add, Formalism.IndefR.Eqv.actO_inv_actO, halfInd_add S T hu (half_sub_of S T h1 hue)]
      · have hqu : IsHalf (cA D e) (actO S T g⁻¹ h⁻¹ u) := isHalf_actO_fp S T _ _ (chalf_sub_of S T h1 hue)
        rw [← hTm.modul _ hG _ hqu]
        congr 1
        funext t
        by_cases hc : actO S T g h t ∈ latAll S T ΛS ΛT ∧ IsHalf e (actO S T g h t)
        · have h1' : symplO S T t (actO S T g⁻¹ h⁻¹ u) = symplO S T (actO S T g h t) u := by
            rw [← Formalism.IndefR.Eqv.symplO_actO S T g h t (actO S T g⁻¹ h⁻¹ u), Formalism.IndefR.Eqv.actO_inv_actO]
          rw [h1', (hd2 u (chalf_sub_of S T h1 hue)).2 hu _ hc.1 hc.2, one_mul]
        · have : halfInd e (latAll S T ΛS ΛT) (actO S T g h t) = 0 := by unfold halfInd; rw [if_neg hc]
          rw [this, mul_zero]
    have hfix : ∀ u ∈ latAll S T ΛS ΛT, (IsHalf e₁ u ∨ IsHalf (cA D e₁) u) →
        heisO ψ S T u (om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) - c • f₀) =
          om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) - c • f₀ := by
      intro u hu hue
      have e1 := hω.om_heis g h (actO S T g⁻¹ h⁻¹ u) _ hG₁
      rw [Formalism.IndefR.Eqv.actO_inv_actO, hfixG u hu hue] at e1
      have e2 : heisO ψ S T u f₀ = f₀ := hvac u hu (hue.imp (half_sub_of S T h1) (chalf_sub_of S T h1))
      rw [← heisL_apply, map_sub, map_smul, heisL_apply, heisL_apply, ← e1, e2]
    obtain ⟨ℓ, hℓ, hℓw⟩ := exists_invForm ψ S T e₁ he₁.2.1 (latAll S T ΛS ΛT) hLL₁ hdY₁ hfX₁ hfY₁ hoY₁
      (fun f hf => by
        obtain ⟨k, hk, hk'⟩ := hlev ψ hψ S T ΛS ΛT hS hT f hf
        exact ⟨k, hk, fun u hu _ => hk' u hu⟩)
      hwθ (fun u hu hue => hfix u hu (Or.inl hue)) (fun u hu hue => hfix u hu (Or.inr hue)) hw0
    apply hℓw
    have hΨSB : IsSBHalf e (latAll S T ΛS ΛT)
        ((fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t)) - halfInd e (latAll S T ΛS ΛT)) := by
      rw [sub_eq_add_neg, ← neg_one_smul ℂ (halfInd e (latAll S T ΛS ΛT))]
      exact (isSBHalf_iff S T).2 (((isSBHalf_iff S T).1 hG).add (((isSBHalf_iff S T).1 hindSB).smul (-1)))
    have hev := evalYZero_zero S T ψ he₁ h1 (latAll S T ΛS ΛT) hΛe₁ hLL₁ hdX₁ hfY₁ Tm hTm.modul hthm ℓ hℓ hΨSB
      (fun t ht h0 => by
        show halfInd e (latAll S T ΛS ΛT) (actO S T g h t) - halfInd e (latAll S T ΛS ΛT) t = 0
        rw [actO_fix S T he.2 h1 hg hh ht h0, sub_self])
    rw [map_sub, map_sub, hf₀T] at hev
    rw [map_sub, map_smul, hsplit ℓ hℓ _ hG₁, smul_eq_mul, ← mul_sub, hev, mul_zero]

  let Tm' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    c⁻¹ • ((om (g, h)).comp (Tm.comp (Formalism.IndefR.Eqv.pull S T g h)))
  have hTm'ap : ∀ Φ, Tm' Φ = c⁻¹ • om (g, h) (Tm (fun t => Φ (actO S T g h t))) := fun Φ => rfl
  have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latAll S T ΛS ΛT) 1 f₀ Tm' := by
    refine ⟨fun Φ hΦ x₀ hx₀ => ?_, fun Φ hΦ y₀ hy₀ => ?_, ?_⟩
    · rw [hTm'ap, hTm'ap]
      have hq : IsHalf e (actO S T g⁻¹ h⁻¹ x₀) := isHalf_actO_fp S T _ _ hx₀
      have e1 : (fun t => Φ (actO S T g h t + x₀)) =
          fun t => Φ (actO S T g h (t + actO S T g⁻¹ h⁻¹ x₀)) := by
        funext t; rw [Formalism.IndefR.Eqv.actO_add, Formalism.IndefR.Eqv.actO_inv_actO]
      show c⁻¹ • om (g, h) (Tm (fun t => Φ (actO S T g h t + x₀))) = _
      rw [e1, hTm.trans _ (hSBp Φ hΦ) _ hq, hω.om_heis g h _ _ (hthm _ (hSBp Φ hΦ)),
        Formalism.IndefR.Eqv.actO_inv_actO, ← heisL_apply, ← heisL_apply, map_smul]
    · rw [hTm'ap, hTm'ap]
      have hq : IsHalf (cA D e) (actO S T g⁻¹ h⁻¹ y₀) := isHalf_actO_fp S T _ _ hy₀
      have e1 : (fun t => ψ (symplO S T (actO S T g h t) y₀) * Φ (actO S T g h t)) =
          fun t => ψ (symplO S T t (actO S T g⁻¹ h⁻¹ y₀)) * Φ (actO S T g h t) := by
        funext t
        rw [← Formalism.IndefR.Eqv.symplO_actO S T g h t (actO S T g⁻¹ h⁻¹ y₀), Formalism.IndefR.Eqv.actO_inv_actO]
      show c⁻¹ • om (g, h) (Tm (fun t => ψ (symplO S T (actO S T g h t) y₀) * Φ (actO S T g h t))) = _
      rw [e1, hTm.modul _ (hSBp Φ hΦ) _ hq, hω.om_heis g h _ _ (hthm _ (hSBp Φ hΦ)),
        Formalism.IndefR.Eqv.actO_inv_actO, ← heisL_apply, ← heisL_apply, map_smul]
    · rw [one_smul, hTm'ap]
      show c⁻¹ • om (g, h) (Tm (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t))) = f₀
      rw [hw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨r, hr, fun Φ hΦ => ?_, fun hstab hnorm => ?_⟩
  · have e1 := huniq Tm' hTm' _ (hSBq Φ hΦ)
    have e2 := huniq Tm hTm _ (hSBq Φ hΦ)
    rw [← e2, hTm'ap] at e1
    have e3 : (fun t => (fun t => Φ (actO S T g⁻¹ h⁻¹ t)) (actO S T g h t)) = Φ := by
      funext t; exact congrArg Φ (Formalism.IndefR.Eqv.actO_actO_inv S T g h t)
    rw [e3] at e1
    rw [← e1, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  · obtain ⟨μ, 𝓕, ⟨hHaar, hFD, -⟩, hn⟩ := hnorm
    have hindeq : (fun t => halfInd e (latAll S T ΛS ΛT) (actO S T g h t)) = halfInd e (latAll S T ΛS ΛT) := by
      funext t
      unfold halfInd
      by_cases ht : IsHalf e t
      · have h2 := (isHalf_actO_iff S T g h t).2 ht
        simp only [hstab t ht, ht, h2, and_true]
      · have h2 : ¬ IsHalf e (actO S T g h t) := fun h' => ht ((isHalf_actO_iff S T g h t).1 h')
        simp only [ht, h2, and_false, if_false]
    rw [hindeq, hf₀T] at hw
    have hU := hω.om_unit μ 𝓕 hHaar hFD (g, h) f₀ hf₀
    rw [hw] at hU
    have hn' : ∫ w in 𝓕, ‖f₀ w‖ ^ 2 ∂μ = 1 := hn
    have hint : Integrable (fun w => ‖f₀ w‖ ^ 2) (μ.restrict 𝓕) := by
      by_contra hni
      rw [integral_undef hni] at hn'
      exact zero_ne_one hn'
    have hI : ∫⁻ w in 𝓕, ‖f₀ w‖ₑ ^ 2 ∂μ = 1 := by
      have h3 := ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun w => by simp only [Pi.zero_apply]; positivity)
      rw [hn', ENNReal.ofReal_one] at h3
      rw [h3]
      congr 1
      funext w
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    have hsm : (fun w => ‖(c • f₀) w‖ₑ ^ 2) = fun w => ‖c‖ₑ ^ 2 * ‖f₀ w‖ₑ ^ 2 := by
      funext w
      rw [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow]
    rw [hsm, lintegral_const_mul' _ _ (by simp), hI, mul_one] at hU
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_eq_one] at hU
    have hcn : ‖c‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 hU
    have hsf : ‖(splitFacO χS χT x y : ℂ)‖ = 1 := Circle.norm_coe _
    rw [hcdef, norm_mul, hsf, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hcn
    exact hcn

end Formalism.IndefR.Fin

end
end

section
namespace Formalism.IndefR.Fin

theorem splitLinF (D : Formalism.BasicNotions.D7) : SplitLin D := splitLin_of (placeLatDual D) (latLevelF D)

end Formalism.IndefR.Fin
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

namespace Formalism.IndefR.Fin.LevelGroupLemmas

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def epsP (P : Finset (Formalism.L2.DIV.Pl D.host.E)) : AF D.host.F := ∑ PP ∈ P, sA (belowPl PP) 1

theorem sA_orth' {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w) :
    sA v (1 : v.adicCompletion D.host.F) * sA w (1 : w.adicCompletion D.host.F) = 0 :=
  algebraMap_AE_eq_zero (D := D) (by rw [map_mul]; exact phiE_orth h)

section Sum

variable {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} {es : Formalism.L2.DIV.Pl D.host.E → AE D}

theorem algebraMap_epsP (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP) :
    algebraMap (AF D.host.F) (AE D) (epsP P) = e + cA D e := by
  rw [epsP, map_sum, he, map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun PP hPP => (below_of_idemAt (hes PP hPP)).symm

open Classical in
theorem single_one_mul_idempotent_eq_zero_of_notMem (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP)
    (hc : e * cA D e = 0) {a : Formalism.L2.DIV.Pl D.host.E} {A : Finset (Formalism.L2.DIV.Pl D.host.E)} (ha : a ∉ A)
    (hsub : insert a A ⊆ P) : sA (belowPl a) (1 : (belowPl a).adicCompletion D.host.F) * epsP A = 0 := by
  rw [epsP, Finset.mul_sum]
  refine Finset.sum_eq_zero fun PP hPP => sA_orth' fun hv => ?_
  have := idemSum_below_inj hes he hc (hsub (Finset.mem_insert_self a A)) (hsub (Finset.mem_insert_of_mem hPP)) hv
  exact ha (this ▸ hPP)

theorem isIdempotentElem_placeIdempotent (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP)
    (hc : e * cA D e = 0) : ∀ A : Finset (Formalism.L2.DIV.Pl D.host.E), A ⊆ P → IsIdempotentElem (epsP A) := by
  classical
  intro A
  induction A using Finset.induction_on with
  | empty => intro _; simp [epsP, IsIdempotentElem]
  | insert a A ha ih =>
    intro hsub
    rw [epsP, Finset.sum_insert ha]
    exact isIdem_add_orth (sA_idem _) (ih ((Finset.subset_insert a A).trans hsub))
      (single_one_mul_idempotent_eq_zero_of_notMem hes he hc ha hsub)

end Sum

section Chain

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
  {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} {es : Formalism.L2.DIV.Pl D.host.E → AE D}

end Chain

theorem vacFixOff (hSL : SplitLin D) (hPM : PlaceModelAt D) (hSOI : SplitOrInert D) : VacFixOffO D :=
  vacFixOff_of hSL hPM hSOI fun _ _ _ _ _ _ _ _ hfS hfT _ _ _ _ hg hh t => actO_mem_latAll_iff hfS hfT hg hh t

end Formalism.IndefR.Fin.LevelGroupLemmas

namespace Formalism.IndefR.Fin

end Formalism.IndefR.Fin

end
end
