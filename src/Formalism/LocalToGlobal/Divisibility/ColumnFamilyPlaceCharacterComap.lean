import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2.Indef

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

namespace DefFam

variable {T T' J : Type} (F : DefFam K G Pl0 T J)

def comap (f : T' → T) (μ0' : T') : DefFam K G Pl0 T' J where
  v0 := F.v0
  μ0 := μ0'
  X := F.X
  R t := F.R (f t)
  L j t := F.L j (f t)
  tr := F.tr

theorem comap_ok [Fintype J] {s : ℕ} (h : F.Ok s) {f : T' → T} (hf : Function.Injective f) (μ0' : T') :
    (F.comap f μ0').Ok s where
  conj := h.conj
  tup_fin := @Finite.of_injective _ _ h.tup_fin f hf
  irr := h.irr
  what₂ t := h.what₂ (f t)
  lifts j t := h.lifts j (f t)

end DefFam

namespace DefFam3

variable {I0 Ty T T' J : Type} (F3 : DefFam3 K G Pl0 I0 Ty T J)

def comap (f : T' → T) (μ0' : T') : DefFam3 K G Pl0 I0 Ty T' J where
  F := F3.F.comap f μ0'
  RI t := F3.RI (f t)
  LI j t := F3.LI j (f t)
  trI := F3.trI

theorem comap_ok_of_injective [Fintype J] {s : ℕ} (h : F3.Ok3 s) {f : T' → T} (hf : Function.Injective f) (μ0' : T') :
    (F3.comap f μ0').Ok3 s where
  ok2 := F3.F.comap_ok h.ok2 hf μ0'
  what₂ t := h.what₂ (f t)
  lifts j t := h.lifts j (f t)

theorem comap_typesSep3_iff [Fintype J] {f : T' → T} {μ0' : T'} (hμ : f μ0' = F3.F.μ0) :
    (F3.comap f μ0').TypesSep3 ↔ F3.TypesSep3 := by
  unfold DefFam3.TypesSep3
  show (∀ p ∈ (F3.RI (f μ0')).ixFin3 F3.F.X, ∀ p' ∈ (F3.RI (f μ0')).ixFin3 F3.F.X, p ≠ p' →
      ∀ j, (F3.LI j (f μ0')).DiffAt (F3.tr3 j p) (F3.tr3 j p')) ↔ _
  rw [hμ]

theorem comap_trISep_iff [Fintype J] {f : T' → T} {μ0' : T'} (hμ : f μ0' = F3.F.μ0) :
    (F3.comap f μ0').TrISep ↔ F3.TrISep := by
  unfold DefFam3.TrISep
  show (∀ j, ∀ p ∈ (F3.RI (f μ0')).ixFin3 F3.F.X, ∀ p' ∈ (F3.RI (f μ0')).ixFin3 F3.F.X,
      (∃ k : (F3.RI (f μ0')).PlI × Ty, p.2 ((F3.RI (f μ0')).plI k.1, k.2) ≠ p'.2 ((F3.RI (f μ0')).plI k.1, k.2)) →
        ∃ k : (F3.LI j (f μ0')).PlI × Ty,
          F3.trI j p.2 ((F3.LI j (f μ0')).plI k.1, k.2) ≠ F3.trI j p'.2 ((F3.LI j (f μ0')).plI k.1, k.2)) ↔ _
  rw [hμ]

end DefFam3

namespace FamIn

variable {T T' : Type} {m : ℕ} (A : FamIn K G Pl0 T m)

def comap (f : T' → T) (μ0' : T') : FamIn K G Pl0 T' m where
  v0 := A.v0
  μ0 := μ0'
  X := A.X
  r := A.r
  t := A.t
  q := A.q
  muVal j τ := A.muVal j (f τ)
  etaVal := A.etaVal
  ok τ := A.ok (f τ)
  MtildeCSD τ := A.MtildeCSD (f τ)
  leftGroupActionRight τ := A.leftGroupActionRight (f τ)
  heckeR τ := A.heckeR (f τ)
  MtCSD j τ := A.MtCSD j (f τ)
  leftGroupActionLift j τ := A.leftGroupActionLift j (f τ)
  heckeL j τ := A.heckeL j (f τ)

end FamIn

namespace FamIn3

variable {I0 Ty T T' : Type} {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m)

def comap (f : T' → T) (μ0' : T') : FamIn3 K G Pl0 I0 Ty T' m where
  A := A3.A.comap f μ0'
  okI τ := A3.okI (f τ)
  heckeRI τ := A3.heckeRI (f τ)
  heckeLI j τ := A3.heckeLI j (f τ)
  trI := A3.trI


end FamIn3

end Gen

section Inst

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)

def TupF.incl {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC) : TupF TU → TupF TC :=
  fun τ => ⟨τ.1, τ.2.imp id fun hm => h hm⟩

theorem TupF.incl_injective {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC) : Function.Injective (TupF.incl h) := by
  intro a b hab
  have hv : (TupF.incl h a).1 = (TupF.incl h b).1 := congrArg Subtype.val hab
  exact Subtype.ext hv

theorem TupF.incl_mu0F {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC) : TupF.incl h (mu0F TU) = mu0F TC := rfl

variable (v0 : InfinitePlace X.K) {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC)
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)



theorem colFam3_comap :
    colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv =
      (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).comap (TupF.incl h) (mu0F TU) := rfl

















include h in

theorem colHyp_restrict (hH : ColHyp W Ch sel v0 TC Xg S0) : ColHyp W Ch sel v0 TU Xg S0 where
  conj := hH.conj
  irr := hH.irr
  commR τ := hH.commR (TupF.incl h τ)
  splitR τ := hH.splitR (TupF.incl h τ)
  commL j τ := hH.commL j (TupF.incl h τ)
  splitL j τ := hH.splitL j (TupF.incl h τ)

include h in

theorem colHyp3_restrict (hH : ColHyp3 W Ch sel v0 TC Xg S0) : ColHyp3 W Ch sel v0 TU Xg S0 where
  base := colHyp_restrict W Ch sel v0 h Xg S0 hH.base
  commAllR τ := hH.commAllR (TupF.incl h τ)
  splitIR τ := hH.splitIR (TupF.incl h τ)
  commAllL j τ := hH.commAllL j (TupF.incl h τ)
  splitIL j τ := hH.splitIL j (TupF.incl h τ)

include h in

theorem column_family_ok_restrict_subtype {s : ℕ} (hO : (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).Ok3 s) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).Ok3 s := by
  exact DefFam3.comap_ok_of_injective _ hO (TupF.incl_injective h) (mu0F TU)

include h in

theorem colFam3_ok_restrict (hH : ColHyp3 W Ch sel v0 TC Xg S0) : (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).Ok3 1 := by
  exact column_family_ok_restrict_subtype (h := h) (hO := colFam3_ok (hH := hH) ..) ..

include h in

theorem colFam3_typesSep3_restrict_iff :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).TypesSep3 ↔ (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).TypesSep3 := by
  rw [colFam3_comap W Ch sel hX v0 h Xg S0 xiVal trIv]
  exact DefFam3.comap_typesSep3_iff (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv) (TupF.incl_mu0F h)

include h in

theorem colFam3_trISep_restrict_iff :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).TrISep ↔ (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).TrISep := by
  rw [colFam3_comap W Ch sel hX v0 h Xg S0 xiVal trIv]
  exact DefFam3.comap_trISep_iff (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv) (TupF.incl_mu0F h)

include h in

theorem colFam3_typesSep_restrict (hH : ColHyp3 W Ch sel v0 TC Xg S0)
    (hI : (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).TrISep) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).TypesSep3 := by
  exact (colFam3_typesSep3_restrict_iff W Ch sel hX v0 h Xg S0 xiVal trIv).mpr
    (colFam3_typesSep' W Ch sel hX v0 TC Xg S0 xiVal trIv hH hI)



def colSubRes3 (Zs : DefSub (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).amb3) :
    DefSub (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).amb3 :=
  ⟨fun t => Zs.Z (TupF.incl h t), fun j t => Zs.Zl j (TupF.incl h t)⟩

variable (Zs : DefSub (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).amb3)







end Inst

end Formalism.L2.DIV
