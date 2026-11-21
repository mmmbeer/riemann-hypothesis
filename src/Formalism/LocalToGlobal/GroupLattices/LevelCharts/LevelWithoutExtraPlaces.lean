import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfChChartsCover
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.FiniteCompG
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.AtGLev
import Formalism.LocalToGlobal.GroupLattices.CloudFilling.CloudBound
import Formalism.LocalToGlobal.HermitianColumns.HermCols
import Formalism.LocalToGlobal.HermitianColumns.TiedQC

section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

structure CharsG (F : Type) [Field F] [NumberField F] (gp : Fin 2 → ℕ) (Z : Type) [CommGroup Z] where
  psi0 : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → AddChar (resV F v) Z
  psi_zero_nontrivial_character : ∀ i v h, psi0 i v h ≠ 1
  chi : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ℕ → (resV F v)ˣ →* Z

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))} {k m t j : ℕ}
    {Z : Type} [CommGroup Z]

theorem awayG_le_comap (p : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    awayG σE J Uloc p ≤ (Uloc v).comap (bc (prV (E := E) v)) :=
  fun x hx => ((mem_awayG σE J Uloc p x).1 hx).2 v hv

def LevAtG.lamG (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0) (ch : CharsG F gp Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z :=
  X.lamGlob hg ch.psi0 ch.chi (awayG σE J Uloc p) (fun i v h => awayG_le_comap p v (not_mem_of_coprime (hp i) v h))

def LevAtG.typeX (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0) (ch : CharsG F gp Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z := (X.lamG hg ch p hp)⁻¹

def LevAtG.psiX (X : LevAtG σE J gp splitG Lb Uloc k m t j) (hg : ∀ i, gp i ≠ 0) (ch : CharsG F gp Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z := (X.typeX hg ch p hp)⁻¹


variable (σE J Uloc) in

def lamQG (Q : Finset (HeightOneSpectrum (𝓞 F))) (lamQ : ∀ v, v ∈ Q → (Uloc v →* Z)) (p : ℕ)
    (hQ : ∀ v ∈ Q, ((p : ℕ) : 𝓞 F) ∉ v.asIdeal) : awayG σE J Uloc p →* Z :=
  prodChar Q Uloc lamQ (awayG σE J Uloc p) (fun v hv => awayG_le_comap p v (hQ v hv))


end Formalism.L2.G
end
end

section
noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

section Loc

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}

def HLoc (H : Subgroup (GL (Fin N) (resV F v))) : Subgroup (GL (Fin N) (v.adicCompletion F)) :=
  congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) H

def lamHLoc {Z : Type} [CommGroup Z] (H : Subgroup (GL (Fin N) (resV F v))) (lam : H →* Z) : HLoc F v H →* Z :=
  congChar _ (algMapV_injective F v) _ _ lam




theorem HLoc_mono {H H' : Subgroup (GL (Fin N) (resV F v))} (h : H ≤ H') : HLoc F v H ≤ HLoc F v H' :=
  Subgroup.map_mono (Subgroup.comap_mono h)


end Loc

section Uni

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (v : HeightOneSpectrum (𝓞 F))
  (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) (fr : GL (Fin N) (v.adicCompletion F))

def HU (H : Subgroup (GL (Fin N) (resV F v))) : Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)) :=
  UPts σE J (v.adicCompletion F) ⊓ (HLoc F v H).comap (toFr v spl fr)


theorem HU_mono {H H' : Subgroup (GL (Fin N) (resV F v))} (h : H ≤ H') : HU σE J v spl fr H ≤ HU σE J v spl fr H' :=
  inf_le_inf_left _ (Subgroup.comap_mono (HLoc_mono F v h))

def lamHU {Z : Type} [CommGroup Z] (H : Subgroup (GL (Fin N) (resV F v))) (lam : H →* Z) : HU σE J v spl fr H →* Z :=
  (lamHLoc F v H lam).comp (((toFr v spl fr).subgroupComap (HLoc F v H)).comp (Subgroup.inclusion inf_le_right))





end Uni

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

structure LevAtGH (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (gp : Fin 2 → ℕ)
    (splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (Lb : Submodule (𝓞 E) (Fin N → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (H : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin N) (resV F v))) where

  frG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → GL (Fin N) (v.adicCompletion F)

  frG_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (x : Fin N → v.adicCompletion F),
    (∃ y ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Lb,
      ∀ b, (splitG i v h (y b)).1 = x b) ↔
      ∀ b, (((frG i v h)⁻¹ : GL (Fin N) (v.adicCompletion F)) : Matrix (Fin N) (Fin N) (v.adicCompletion F)).mulVec x b ∈
        v.adicCompletionIntegers F

  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
    Uloc v = HU σE J v (splitG i v h) (frG i v h) (H i v h)

variable {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))}
    {H : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin N) (resV F v))}
    {Z : Type} [CommGroup Z]

def LevAtG.toH {k m t j : ℕ} (X : LevAtG σE J gp splitG Lb Uloc k m t j) :
    LevAtGH σE J gp splitG Lb Uloc (fun _ v _ => JXbar (resV F v) N k m t j) where
  frG := X.frG
  frG_lat := X.frG_lat
  Uloc_g := X.Uloc_g

def LevAtGH.lamV (X : LevAtGH σE J gp splitG Lb Uloc H) (lam : ∀ i v h, H i v h →* Z) (i : Fin 2)
    (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) : Uloc v →* Z :=
  (lamHU σE J v (splitG i v h) (X.frG i v h) (H i v h) (lam i v h)).comp (Subgroup.inclusion (le_of_eq (X.Uloc_g i v h)))

def LevAtGH.lamGlob (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z)
    (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hUp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      Up ≤ (Uloc v).comap (bc (prV (E := E) v))) : Up →* Z :=
  ∏ i : Fin 2, prodChar (placesOver F (gp i)) Uloc
    (fun v hv => X.lamV lam i v ((mem_placesOver F (gp i) (hg i) v).1 hv))
    Up (fun v hv => hUp i v ((mem_placesOver F (gp i) (hg i) v).1 hv))



def LevAtGH.lamG (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z :=
  X.lamGlob hg lam (awayG σE J Uloc p) (fun i v h => awayG_le_comap p v (not_mem_of_coprime (hp i) v h))

def LevAtGH.typeX (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z := (X.lamG hg lam p hp)⁻¹

def LevAtGH.psiX (X : LevAtGH σE J gp splitG Lb Uloc H) (hg : ∀ i, gp i ≠ 0) (lam : ∀ i v h, H i v h →* Z) (p : ℕ)
    (hp : ∀ i, Nat.Coprime p (gp i)) : awayG σE J Uloc p →* Z := (X.typeX hg lam p hp)⁻¹


def CharsG.lamX (ch : CharsG F gp Z) (N k m t j : ℕ) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) :
    JXbar (resV F v) N k m t j →* Z := lamXbar (resV F v) N k m t j (ch.psi0 i v h) (ch.chi i v h)



theorem LevAtGH.le_top (X : LevAtGH σE J gp splitG Lb Uloc H) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F))
    (h : (gp i : 𝓞 F) ∈ v.asIdeal) : Uloc v ≤ HU σE J v (splitG i v h) (X.frG i v h) ⊤ := by
  rw [X.Uloc_g i v h]
  exact HU_mono σE J v _ _ (_root_.le_top)

end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

def levelWithoutExtraPlaces {S : HSpace E} {T f : ℕ} (X : Formalism.L2.Herm.StepLevel sp.cm S gp T f) :
    Formalism.L2.Herm.StepLevelQ sp.cm S gp T f ∅ where
  Lb := X.Lb
  Lb_fin := X.Lb_fin
  Lb_span := X.Lb_span
  Lb_int := X.Lb_int
  Lb_dual := X.Lb_dual
  Lb_index := X.Lb_index
  Uloc := X.Uloc
  Uloc_lev := X.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT _ => X.Uloc_hyp v h0 h1 hT
  Uloc_g := X.Uloc_g
  UlocAlt := X.UlocAlt
  Uloc_Q := fun v hv => absurd hv (Finset.notMem_empty v)
  U := X.U
  U_eq := X.U_eq

structure StepX (I : LocId L p nV W Qq) (Z : Type) [CommGroup Z] (T f i : ℕ) where

  Q : Finset (HeightOneSpectrum (𝓞 F))
  Q_p : ∀ v ∈ Q, ((p : ℕ) : 𝓞 F) ∉ v.asIdeal
  Q_g : ∀ v ∈ Q, ∀ a, (gp a : 𝓞 F) ∉ v.asIdeal
  prime_not_mem_places : ∀ v ∈ Q, (T : 𝓞 F) ∉ v.asIdeal

  lev : Formalism.L2.Herm.StepLevelQ sp.cm (sp.X i) gp T f Q

  HG : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin (sp.X i).rank) (resV F v))

  atG : LevAtGH sp.cm.sig (sp.X i).gram gp L.splitG lev.Lb lev.Uloc HG

  lamG : ∀ a v h, HG a v h →* Z

  typQ : ∀ v, v ∈ Q → (lev.Uloc v →* Z)

  fr : FrS I lev.Lb

  fin : Finite (ClassSet (Formalism.L2.Herm.UFin sp.cm (sp.X i)) (lev.U.subgroupOf (Formalism.L2.Herm.UAf sp.cm (sp.X i))))

def StepX.type {I : LocId L p nV W Qq} {Z : Type} [CommGroup Z] {T f i : ℕ} (Sx : StepX I Z T f i)
    (hg : ∀ a, gp a ≠ 0) (hp : ∀ a, Nat.Coprime p (gp a)) :
    awayG sp.cm.sig (sp.X i).gram Sx.lev.Uloc p →* Z :=
  Sx.atG.typeX hg Sx.lamG p hp * lamQG sp.cm.sig (sp.X i).gram Sx.lev.Uloc Sx.Q Sx.typQ p Sx.Q_p

def StepX.toStepAt {I : LocId L p nV W Qq} {O : Type} [CommRing O] {T f i : ℕ} (Sx : StepX I Oˣ T f i)
    (hg : ∀ a, gp a ≠ 0) (hp : ∀ a, Nat.Coprime p (gp a)) : StepAt I O (sp.X i).rank where
  J := (sp.X i).gram
  Lb := Sx.lev.Lb
  Uloc := Sx.lev.Uloc
  fr := Sx.fr
  ψ := (Sx.type hg hp)⁻¹
  eps := 1
  fin := finite_compG sp.cm.sig (sp.X i).gram Sx.lev.Uloc p Sx.lev.U (fun x hx => (Sx.lev.U_eq x).1 hx) Sx.fin

def StepX.ofFlag {I : LocId L p nV W Qq} {Z : Type} [CommGroup Z] {T f i : ℕ}
    (Q : Finset (HeightOneSpectrum (𝓞 F))) (Q_p : ∀ v ∈ Q, ((p : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (Q_g : ∀ v ∈ Q, ∀ a, (gp a : 𝓞 F) ∉ v.asIdeal) (prime_not_mem_places : ∀ v ∈ Q, (T : 𝓞 F) ∉ v.asIdeal)
    (lev : Formalism.L2.Herm.StepLevelQ sp.cm (sp.X i) gp T f Q)
    (atG : LevAtG sp.cm.sig (sp.X i).gram gp L.splitG lev.Lb lev.Uloc R.k R.m R.t i) (ch : CharsG F gp Z)
    (typQ : ∀ v, v ∈ Q → (lev.Uloc v →* Z)) (fr : FrS I lev.Lb)
    (fin : Finite (ClassSet (Formalism.L2.Herm.UFin sp.cm (sp.X i)) (lev.U.subgroupOf (Formalism.L2.Herm.UAf sp.cm (sp.X i))))) :
    StepX I Z T f i where
  Q := Q
  Q_p := Q_p
  Q_g := Q_g
  prime_not_mem_places := prime_not_mem_places
  lev := lev
  HG := fun _ v _ => JXbar (resV F v) (sp.X i).rank R.k R.m R.t i
  atG := atG.toH
  lamG := ch.lamX (sp.X i).rank R.k R.m R.t i
  typQ := typQ
  fr := fr
  fin := fin

end Generic

section Record

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem rank_step (D : D7) (i : ℕ) (hi : i < D.R.m) :
    D.R.k - 1 + (i + 1) * (D.R.t + 1) + 1 = (D.sp.X (i + 1)).rank := by
  rw [D.sp.X_rank (i + 1) hi]
  have := k_pred D.R
  simp only [Ranks.N]
  omega

abbrev levelsRec (D : D7) (u : D.what₂.Word) (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ) (c : ℕ) (hc : CloudBound D u c)
    (hg : ∀ a, D.host.g a ≠ 0) (hp : ∀ a, Nat.Coprime p (D.host.g a))
    (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
    (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I Oˣ (D.mem u).A.T D.R.f (i + 1)) :
    Levels (fillsRec D u h hS r L I ψ y e c hc) :=
  levelsOfCh hS r (fun v s => lamRec D u (posG (zPsi D.R.toFrame h) ⟨v, s⟩)) (fun _ _ => lamRec_anti D u _) (k_pred D.R) I ψ y e
    (fillsRec D u h hS r L I ψ y e c hc) D.R.m (fun i => (D.sp.X (i + 1)).rank) (fun i hi => rank_step D i hi) Cb
    (fun i hi β => (Sx i hi β).toStepAt hg hp)

structure StepMore (D : D7) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
    (u : D.what₂.Word) (μ : D.what₂.Tup)
    {L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ}
    (I : LocId L p nV W Qq) (Z : Type) [CommGroup Z] (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) where
  Q_p : ∀ v ∈ T.Q μ, ((p : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal
  Q_g : ∀ v ∈ T.Q μ, ∀ a, (D.host.g a : 𝓞 D.host.F) ∉ v.asIdeal
  prime_not_mem_places : ∀ v ∈ T.Q μ, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal
  HG : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin (D.sp.X i).rank) (resV D.host.F v))
  atG : LevAtGH D.sp.cm.sig (D.sp.X i).gram D.host.g L.splitG (T.lev u μ i h1 hm β).Lb (T.lev u μ i h1 hm β).Uloc HG
  lamG : ∀ a v h, HG a v h →* Z
  typQ : ∀ v, v ∈ T.Q μ → ((T.lev u μ i h1 hm β).Uloc v →* Z)
  fr : FrS I (T.lev u μ i h1 hm β).Lb

def stepXTw (D : D7) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    {L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ}
    (I : LocId L p nV W Qq) (Z : Type) [CommGroup Z] (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i)
    (M : StepMore D T u μ I Z i h1 hm β) : StepX I Z (D.mem u).A.T D.R.f i where
  Q := T.Q μ
  Q_p := M.Q_p
  Q_g := M.Q_g
  prime_not_mem_places := M.prime_not_mem_places
  lev := T.lev u μ i h1 hm β
  HG := M.HG
  atG := M.atG
  lamG := M.lamG
  typQ := M.typQ
  fr := M.fr
  fin := T.finite_cls u μ hμ i h1 hm β

end Record

end Formalism.L2.G
end
end
