import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FrobOrderSpec
import Formalism.LocalToGlobal.GroupLattices.TiedRec
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CmpHyp0P
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieFin
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.BlockRationalityField
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BlockRatReal
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.WeylLatticeDescentHolds
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.ColSpanMulUnit
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.SelfDualCongr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroOfSetting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocIdOfCompletions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddCharIsIntegral

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

section Ext

variable {Os Ks O Kf O' Kf' : Type} [CommRing Os] [Field Ks] [Algebra Os Ks] [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf']
  [Algebra O' Kf']

theorem extMap_φ (X : ExtOf Os Ks O Kf) (eO : O ≃+* O') (eK : Kf ≃+* Kf')
    (hc : ∀ x, eK (algebraMap O Kf x) = algebraMap O' Kf' (eO x)) (hfrac : IsFractionRing O' Kf')
    (hcomp : IsAdicComplete (IsLocalRing.maximalIdeal O') O') (x : Os) :
    (X.map eO eK hc hfrac hcomp).φ x = eO (X.φ x) := rfl

theorem extMap_φK (X : ExtOf Os Ks O Kf) (eO : O ≃+* O') (eK : Kf ≃+* Kf')
    (hc : ∀ x, eK (algebraMap O Kf x) = algebraMap O' Kf' (eO x)) (hfrac : IsFractionRing O' Kf')
    (hcomp : IsAdicComplete (IsLocalRing.maximalIdeal O') O') (y : Ks) :
    (X.map eO eK hc hfrac hcomp).φK y = eK (X.φK y) := rfl

end Ext

section Ties

abbrev RingTie := @Formalism.L2.G.RingCompatibleAt

abbrev LocalIs := @Formalism.L2.G.GatIs

abbrev AllTies := @Formalism.L2.G.GroupCompatibilityAll

alias standardSub_of_ringTie := Formalism.L2.G.stdSubAt_of_ring

alias localIs_of_hyperspecial := Formalism.L2.G.gatIs_recG

alias castLevelTie_basis := Formalism.L2.G.levTieOf_fr

alias castLevelTie_splitting := Formalism.L2.G.levTieOf_spl

alias tieEmbedding_castLevelTie := Formalism.L2.G.tieIw_levTieOf

alias ringTie_record := Formalism.L2.G.ringTied_recC

alias hermTies_level := Formalism.L2.G.fullTiedC_base

alias localIs_record := Formalism.L2.G.gatIs_recC

alias hermTies_basis_rational := Formalism.L2.G.frRat_C

alias comparison_embedding_eq := Formalism.L2.G.locAt_iw_C

alias comparison_positions := Formalism.L2.G.pos_C

end Ties

section Bridge


theorem pack_eq (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
    (h5 : 5 ≤ D.what₂.places.resChar w) (h2 : 2 ≤ nFr D (D.what₂.places.resChar w))
    (he : Even (nFr D (D.what₂.places.resChar w)))
    (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
    (ψ : Formalism.L2.Herm.awayFrom₂ Lc (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ) :
    pack D u Lc w h5 h2 he I ψ = locPackC D u Lc w h5 h2 he I ψ := by
  first
    | with_reducible rfl
    | (delta pack locPackC frobOrder nFr; with_reducible rfl)

end Bridge

section Record

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)





example : Joints.StdSubAt (recC D sc Ce Lc I ψ hd) :=
  standardSub_of_ringTie _ (ringTie_record D sc Ce Lc I ψ hd)

example (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    LocalIs (recC D sc Ce Lc I ψ hd) Lc u w hg :=
  localIs_of_hyperspecial D sc Ce Lc (packC D Lc I ψ) hd Lc (fun _ => rfl)
    (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)) u w hg

end Record

abbrev IsConcrete := @Formalism.L2.G.IsRecC

alias IsConcrete.intro := Formalism.L2.G.IsRecC.intro




example {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {v : Fin (D.gat u w hg).P.nV} (h : RingTie D u w hg v) :
    Nonempty (WQ (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) ≃+* (D.gat u w hg).P.W v) :=
  h.elim fun e _ => ⟨e⟩

example {D : D7} {Gt : GatTies D} {c : LatCmp D} : IsConcrete D Gt c ↔ IsRecC D Gt c := Iff.rfl

end GlobalTheory.Mem.LocalPack
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace GlobalTheory.Mem.LocalPack.Test

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

theorem exists_place_over (F : Type) [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∈ v.asIdeal := by
  have hp0 : (p : 𝓞 F) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hnu : ¬ IsUnit (p : 𝓞 F) := by
    intro h
    have h1 : IsUnit (Algebra.norm ℤ (p : 𝓞 F)) := h.map _
    have h2 : Algebra.norm ℤ (p : 𝓞 F) = (p : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 F) (p : ℤ)
      simpa using this
    rw [h2, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq] at h1
    exact hp.ne_one (by simpa using h1)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(p : 𝓞 F)}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : (p : 𝓞 F) ∈ M := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨M, hM.isPrime, fun h => hp0 (by simpa [h] using hmem)⟩, hmem⟩


set_option maxHeartbeats 4000000 in

theorem coefficient_ring {D : D7} {Gt : GatTies D} {c : LatCmp D} (h : IsConcrete D Gt c) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (D.gat u w hg).O = ORec D w (frobOrder D (D.what₂.places.resChar w)) := by
  obtain ⟨D0, sc, Lc, I, ψ, hd, H0, hL, T, B, hBs, hB, iK, lam, hK, hPos, CH, heq⟩ := h
  cases heq
  rfl





section Reduction

open Formalism.L2.G.Cmp Formalism.L2.G.RelativeIndexFlags

theorem block_rational : Formalism.L2.G.BlockRationalityField := by
  intro p O Kf _ _ _ _ _ P Tau _ n LL _ h pos G M embLL lam hW hM
  exact blockRatReal P.lam0 h pos G M embLL (fun τ => (lam τ).w) (fun τ => (lam τ).anti) hW hM

variable (D : D7) (sc : Scale)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc 1 (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
  (H0 : Formalism.L2.Herm.Herm0 (recC D sc 1 Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
  (T : ∀ u : D.what₂.Word, Forms0 (recC D sc 1 Lc I ψ hd) u)
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc 1 Lc I ψ hd) B)
  (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
      (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
  (iK : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    KfRec D w (nFr D (D.what₂.places.resChar w)) →+* ℂ_[D.what₂.places.resChar w])
  (lam : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w])
  (hK : ∀ u w hg (z : D.what₂.LL), iK u w hg (embRec D w (nFr D (D.what₂.places.resChar w)) z) =
    lamV (lam u w hg) (D.what₂.embLL z))
  (hPos : ∀ u w hg, (packC D Lc I ψ u w hg).posOK (iK u w hg) (lam u w hg))

set_option maxHeartbeats 32000000 in
include hK hPos in

theorem comparison_statements (hJ : ∀ u, Joint0 H0.lev0 u (T u))
    (h0 : ∀ u, LevelZeroCharacterRational (D := recC D sc 1 Lc I ψ hd) T u)
    (hψ : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (Lc u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        ((cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB).embW u w hg) (ψ u w hg)) :
    CmpHyp0P T (gatTiesC D sc 1 Lc I ψ hd) (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB) := by
  have hpos := fun u w hg v s x => pos_C D sc 1 Lc I ψ hd H0 hL B hBs hB iK lam hK hPos u w hg v s x
  have hs : ∀ u, SameUloc (hermitianLevelZeroOfRecursion D sc 1 Lc I ψ hd H0 hL) T u :=
    fun u => sameUloc_of_joint (hermitianLevelZeroOfRecursion D sc 1 Lc I ψ hd H0 hL) T u (hJ u)
  have N : CmpLeft D sc 1 Lc I ψ hd H0 hL T B hBs hB :=
    { same := hs
      blk := fun u w hg => blkRatRec_of_stmt block_rational _ _ u w hg B
      psi0 := h0
      chi := chi_C D sc 1 Lc I ψ hd H0 hL T B hBs hB hψ
      valInt := valIntRec_of weylLatticeDescent_holds
        (fun u w hg => ex_C_blk D sc 1 Lc I ψ hd H0 hL T B hBs hB u (hs u) w hg
          (blkRatRec_of_stmt block_rational _ _ u w hg B) (h0 u))
        (fun u w hg => frac_of_gatIs _ u w hg (gatIs_recC D sc 1 Lc I ψ hd H0 hL
          (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)) u w hg))
        (restExB _)
        (restLatO_of hpos (restLatW_of (D := recC D sc 1 Lc I ψ hd) T (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB) (fun u => hJ u))
          (restGramW_of (D := recC D sc 1 Lc I ψ hd) T (cmpInC D sc 1 Lc I ψ hd H0 hL B hBs hB)))
        (restChi_of (D := recC D sc 1 Lc I ψ hd) T h0) }
  exact N.toHyp0P hpos

set_option maxHeartbeats 32000000 in
include hBs hB hK hPos hL in

theorem exists_isConcrete (hJ : ∀ u, Joint0 H0.lev0 u (T u))
    (h0 : ∀ u, LevelZeroCharacterRational (D := recC D sc 1 Lc I ψ hd) T u)
    (hψ : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (Lc u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        (embRec D w (nFr D (D.what₂.places.resChar w))) (ψ u w hg)) :
    ∃ c, IsConcrete (recC D sc 1 Lc I ψ hd) (gatTiesC D sc 1 Lc I ψ hd) c :=
  ⟨_, IsConcrete.intro D sc Lc I ψ hd H0 hL T B hBs hB iK lam hK hPos
    (comparison_statements D sc Lc I ψ hd H0 hL T B hBs hB iK lam hK hPos hJ h0 hψ) rfl⟩

end Reduction




set_option maxHeartbeats 32000000 in

theorem exists_concrete_of_record (D : D7) (L0 : LevelData D) (T : ∀ u : D.what₂.Word, Forms0 D u)
    (hS : Formalism.L2.Herm.StdTied D) (hJ : ∀ u, Joint0 L0 u (T u)) (h0 : ∀ u, LevelZeroCharacterRational T u)
    (hb : ∀ u, ∃ 𝔞 : Ideal (𝓞 D.host.E), (L0 u).Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E)
      (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (L0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0)
    (sc : Scale) : ∃ I ψ hd c, IsConcrete (recC D sc 1 L0 I ψ hd) (gatTiesC D sc 1 L0 I ψ hd) c := by
  obtain ⟨B, hB⟩ := exists_stdB_of_tied D hS
  choose 𝔞 h𝔞 using hb
  choose I0 iK lam hK hPos using fun u w hg => GlobalTheory.PlaceOrbit.exists_locId D u (L0 u) w hg
  choose ψ hψ using fun u w hg => GlobalTheory.Mem.AwayChar.exists_psi D L0 T hJ h0 u w hg
  let I := fun u w hg => locIdStd D u w hg (I0 u w hg) B hB (𝔞 u) (h𝔞 u)
  have hd : ∀ u w h, ((packC D L0 I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
      (epSc D.R sc 1 (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0 := by
    intro u w h
    exact GlobalTheory.ClassRank.pack_d_eq D L0 T hJ u w h _ _ _ _
  refine ⟨I, ψ, hd, ?_⟩
  refine exists_isConcrete D sc L0 I ψ hd ⟨L0, levTieG D sc 1 L0 (packC D L0 I ψ) hd⟩ (fun _ => rfl)
    (formsOfRecursion D sc 1 L0 I ψ hd T) B hB (fun _ _ _ _ _ => rfl) iK lam hK ?_ ?_ ?_ ?_
  · intro u w hg
    exact hPos u w hg (ψ u w hg)
  · exact fun u => hJ u
  · exact fun u => h0 u
  · exact fun u w hg => hψ u w hg

end GlobalTheory.Mem.LocalPack.Test
end
end
