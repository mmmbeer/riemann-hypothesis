import Formalism.LocalToGlobal.NormalizedHeckeFactors.NormalizedHeckeData
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingSpecSidedEmbeddingFixedField
import Formalism.LocalToGlobal.NormalizedHeckeFactors.ValLeOneOfIsIntegral
import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
import Formalism.LocalToGlobal.NormalizedHeckeFactors.WittCoreInclusionMulVecMemLatticeCompletionAtPla
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsGoodPlacesEveryConjugate
import Formalism.LocalToGlobal.LocalInduction.BridgeInd
import Formalism.LocalToGlobal.GaloisLevelStructure.LinkChar

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace Formalism.L2

abbrev TwPick (D : D7) (i : D.ntw.Tw) : Type :=
  Σ (Q : Finset (PlE D.host)) (k' : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ

def ExpHyp (D : D7) (I : TwIn D) (i : D.ntw.Tw) : Prop :=
  Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0 ∧ D.ntw.NonzeroIndexPlace i ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i ∧ I.Ok i

open Classical in

def ExpGood (D : D7) (I : TwIn D) (A : Finset (PlE D.host)) (i : D.ntw.Tw) (p : TwPick D i) : Prop :=
  IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 i (twEps D i) (I.S i) A p.1 p.2.1 p.2.2

open Classical in

theorem expGood_anti {D : D7} {I : TwIn D} {A A' : Finset (PlE D.host)} (hA : A ⊆ A') {i : D.ntw.Tw} {p : TwPick D i}
    (h : ExpGood D I A' i p) : ExpGood D I A i p := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  refine And.intro (And.intro h1 (And.intro (h2.mono_right ?_) h3)) h4
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  rcases hx with hx | hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr (hA hx))

theorem exists_expPick (D : D7) (I : TwIn D) (A : Finset (PlE D.host)) (i : D.ntw.Tw) :
    ∃ p : TwPick D i, ExpHyp D I i → ExpGood D I A i p := by
  by_cases h : ExpHyp D I i
  · obtain ⟨h1, h2, h3, h4⟩ := h
    unfold Formalism.MainNotions.IntegralHeckeEveryConjugate at h1
    obtain ⟨Q, k', ψ', hg⟩ := h1 i h2 h3 (twEps D i) (twEps_pos D i) h4.1 (I.S i) h4.2 A
    refine ⟨⟨Q, k', ψ'⟩, fun _ => ?_⟩
    have hg1 := hg 1 (by simp)
    rw [zpow_one] at hg1
    exact hg1
  · exact ⟨⟨∅, 0, 1⟩, fun h' => absurd h' h⟩

def expPick (D : D7) (I : TwIn D) (A : Finset (PlE D.host)) (i : D.ntw.Tw) : TwPick D i :=
  Classical.choose (exists_expPick D I A i)

theorem expPick_good (D : D7) (I : TwIn D) (A : Finset (PlE D.host)) (i : D.ntw.Tw) (h : ExpHyp D I i) :
    ExpGood D I A i (expPick D I A i) := Classical.choose_spec (exists_expPick D I A i) h

abbrev TwAv (D : D7) : Type := D.ntw.Tw → Finset (PlE D.host)

def avD (D : D7) (Av : TwAv D) (i : D.ntw.Tw) : Finset (PlE D.host) :=
  open Classical in AvRec D ∪ Av i

theorem avRec_subset_avD (D : D7) (Av : TwAv D) (i : D.ntw.Tw) : AvRec D ⊆ avD D Av i := by
  classical
  intro v hv
  unfold avD
  exact Finset.mem_union_left _ hv


def placesOverQ0 (D : D7) : Finset (PlE D.host) :=
  (placesOver_finite_av D.host.E (AbsolutelyIrreducibleSpan.q0 D) (Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1.ne_zero).toFinset



def avOver (D : D7) (s : Finset ℕ) : Finset (PlE D.host) :=
  (Set.Finite.biUnion (s := ((s.filter (· ≠ 0) : Finset ℕ) : Set ℕ)) (t := fun p => placesOver D.host.E p)
    (Finset.finite_toSet _) fun p hp => placesOver_finite_av _ p (Finset.mem_filter.1 hp).2).toFinset

theorem mem_avOver {D : D7} (s : Finset ℕ) (v : PlE D.host) :
    v ∈ avOver D s ↔ ∃ p ∈ s, p ≠ 0 ∧ v ∈ placesOver D.host.E p := by
  simp only [avOver, Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop, Finset.mem_coe,
    Finset.mem_filter, and_assoc]

def avPrimesDesign (D : D7) (i : D.ntw.Tw) : Finset ℕ :=
  insert 2 (insert (D.ntw.l i) (insert (AbsolutelyIrreducibleSpan.q0 D) (NumberField.discr D.host.E).natAbs.primeFactors))

theorem prime_of_mem_avPrimesDesign {D : D7} {i : D.ntw.Tw} {p : ℕ} (hp : p ∈ avPrimesDesign D i) : p.Prime := by
  unfold avPrimesDesign at hp
  simp only [Finset.mem_insert, Nat.mem_primeFactors] at hp
  rcases hp with rfl | rfl | rfl | ⟨hp, -, -⟩
  · exact Nat.prime_two
  · exact Fact.out
  · exact (Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1
  · exact hp

def avDesign (D : D7) : TwAv D := fun i => avOver D (avPrimesDesign D i)

theorem mem_avDesign {D : D7} (i : D.ntw.Tw) (v : PlE D.host) :
    v ∈ avDesign D i ↔ ∃ p ∈ avPrimesDesign D i, v ∈ placesOver D.host.E p := by
  show v ∈ avOver D (avPrimesDesign D i) ↔ _
  rw [mem_avOver]
  constructor
  · rintro ⟨p, hp, -, hv⟩
    exact ⟨p, hp, hv⟩
  · rintro ⟨p, hp, hv⟩
    exact ⟨p, hp, (prime_of_mem_avPrimesDesign hp).ne_zero, hv⟩




def SidePl (D : D7) (w : D.what₂.places.Pl) (i : D.ntw.Tw) (s : Bool) : Prop :=
  ∀ x : D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔
    (if s then D.ntw.emb0 i x else D.ntw.emb0b i x) ∈ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).range

def twPackPow (D : D7) (a : ℤ) (p : TwPack D) : TwPack D :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2 ^ a⟩

def fracOe (D : D7) (C : NChoice D) (w : D.what₂.places.Pl) : FractionRing (D.ntw.O0 (C.twI w)) →+* FractionRing (C.Oe w) :=
  IsFractionRing.map (j := (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)).comp
      ((algebraMap (D.ntw.O (C.twI w)) (D.ntw.Ok (C.twI w) (C.k' w))).comp (algebraMap (D.ntw.O0 (C.twI w)) (D.ntw.O (C.twI w)))))
    ((C.Oe_inj w).comp ((D.ntw.Ok_inj (C.twI w) (C.k' w)).comp (D.ntw.O_inj (C.twI w))))

structure NChoiceTied (D : D7) (C : NChoice D) (I : TwIn D) (Av : TwAv D) : Prop where
  twI_conj : ∀ w, C.twI (D.what₂.places.conj w) = C.twI w
  sd_place : ∀ w, TwistedAt D w → SidePl D w (C.twI w) (C.sd w)
  emb_side : ∀ w, TwistedAt D w → ∀ (x : D.LL0), C.embW w (x : D.what₂.LL) =
    fracOe D C w (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x)
  sd_conj : ∀ w, TwistedAt D w → D.what₂.places.conj w ≠ w → C.sd (D.what₂.places.conj w) = !C.sd w
  one : ∀ w w', TwistedAt D w → TwistedAt D w' → C.twI w' = C.twI w →
    ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (C.twI w)) ∧ NChoicePack C w' = twPackPow D a (NChoicePack C w)
  good : ∀ w, TwistedAt D w → ExpHyp D I (C.twI w) →
    ExpGood D I (avD D Av (C.twI w)) (C.twI w) ⟨C.Q w, C.k' w, BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w)⟩
  conj : ∀ w, TwistedAt D w → NChoicePack C (D.what₂.places.conj w) = NChoicePack C w

structure NChoicePick (D : D7) (C : NChoice D) (I : TwIn D) (Av : TwAv D) : Prop where
  twI_conj : ∀ w, C.twI (D.what₂.places.conj w) = C.twI w
  sd_place : ∀ w, SidePl D w (C.twI w) (C.sd w)
  emb_side : ∀ w (x : D.LL0), C.embW w (x : D.what₂.LL) =
    fracOe D C w (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x)
  sd_conj : ∀ w, D.what₂.places.conj w ≠ w → C.sd (D.what₂.places.conj w) = !C.sd w
  pick : ∀ w, TwistedAt D w → NChoicePack C w = ⟨C.twI w, expPick D I (avD D Av (C.twI w)) (C.twI w)⟩

variable {D : D7} {C : NChoice D} {I : TwIn D} {Av : TwAv D}

theorem twPackPow_one (p : TwPack D) : twPackPow D 1 p = p := by
  rcases p with ⟨i, Q, k, ψ⟩
  simp only [twPackPow, zpow_one]

theorem one_of_pack_eq {p p' : TwPack D} (n : ℕ) (h : p' = p) : ∃ a : ℤ, Nat.Coprime a.natAbs n ∧ p' = twPackPow D a p := ⟨1, by simp, by rw [h, twPackPow_one]⟩

theorem NChoiceTied.Q_eq (hT : NChoiceTied D C I Av) {w w' : D.what₂.places.Pl} (hw : TwistedAt D w)
    (hw' : TwistedAt D w') (h : C.twI w' = C.twI w) : C.Q w' = C.Q w := by
  obtain ⟨a, -, ha⟩ := hT.one w w' hw hw' h
  exact congrArg (fun p : TwPack D => p.2.1) ha




theorem NChoicePick.pick_eq (hT : NChoicePick D C I Av) (w : D.what₂.places.Pl) (hw : TwistedAt D w) :
    (⟨C.Q w, C.k' w, BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w)⟩ : TwPick D (C.twI w)) = expPick D I (avD D Av (C.twI w)) (C.twI w) := by
  have h := hT.pick w hw
  unfold NChoicePack twPack at h
  exact eq_of_heq (Sigma.mk.inj_iff.1 h).2




theorem NChoicePick.tied (hT : NChoicePick D C I Av) : NChoiceTied D C I Av where
  twI_conj := hT.twI_conj
  sd_place w _ := hT.sd_place w
  emb_side w _ := hT.emb_side w
  sd_conj w _ := hT.sd_conj w
  one w w' hw hw' h := one_of_pack_eq _ (by rw [hT.pick w' hw', hT.pick w hw, h])
  good w hw hE := by
    have hG := expPick_good D I (avD D Av (C.twI w)) (C.twI w) hE
    rw [← hT.pick_eq w hw] at hG
    exact hG
  conj w hw := by rw [hT.pick _ ((twistedAt_conj D w).2 hw), hT.pick w hw, hT.twI_conj w]


open Classical in

theorem disjoint_av_of_tied (hT : NChoiceTied D C I Av) (hconds : Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0)
    (w : D.what₂.places.Pl) (hw : TwistedAt D w) (hW1 : D.ntw.NonzeroIndexPlace (C.twI w))
    (hset : BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w)) (hI : I.Ok (C.twI w)) :
    Disjoint (C.Q w) (avD D Av (C.twI w)) := by
  classical
  obtain ⟨⟨-, hd, -⟩, -⟩ := hT.good w hw (And.intro hconds (And.intro hW1 (And.intro hset hI)))
  refine hd.mono_right ?_
  intro x hx
  simp only [Finset.mem_union]
  exact Or.inr (Or.inr hx)

theorem NChoiceTied.mono {Av' : TwAv D} (hT : NChoiceTied D C I Av) (h : ∀ i, Av' i ⊆ Av i) : NChoiceTied D C I Av' where
  twI_conj := hT.twI_conj
  sd_place := hT.sd_place
  emb_side := hT.emb_side
  sd_conj := hT.sd_conj
  one := hT.one
  good w hw hE := by
    classical
    refine expGood_anti ?_ (hT.good w hw hE)
    unfold avD
    exact Finset.union_subset_union (subset_refl _) (h _)
  conj := hT.conj







theorem emb0_mem_maximalIdeal_iff_val_pos_of_sidePl (D : D7) (w : D.what₂.places.Pl) (i : D.ntw.Tw) (h : SidePl D w i true)
    (x : D.LL0) :
    (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i x) ↔
    0 < D.what₂.places.val w (x : D.what₂.LL) := by
  have key : ∀ z : D.LL0, 0 ≤ D.what₂.places.val w (z : D.what₂.LL) ↔
      D.ntw.emb0 i z ∈ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).range := fun z => by
    simpa using h z
  have hinj := IsFractionRing.injective (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))
  have hmul : ∀ z : D.LL0, z ≠ 0 →
      D.what₂.places.val w (z : D.what₂.LL) + D.what₂.places.val w ((z⁻¹ : D.LL0) : D.what₂.LL) = 0 := by
    intro z hz
    rw [← AddValuation.map_mul, IntermediateField.coe_inv, mul_inv_cancel₀ (by exact_mod_cast hz),
      AddValuation.map_one]
  constructor
  · rintro ⟨y, hy, hyx⟩
    by_cases hx : x = 0
    · subst hx; simp
    by_contra hlt
    have h0 : 0 ≤ D.what₂.places.val w (x : D.what₂.LL) := (key x).2 ⟨y, hyx⟩
    have heq : D.what₂.places.val w (x : D.what₂.LL) = 0 := le_antisymm (not_lt.1 hlt) h0
    have hinv : 0 ≤ D.what₂.places.val w ((x⁻¹ : D.LL0) : D.what₂.LL) := by
      have := hmul x hx
      rw [heq, zero_add] at this
      rw [this]
    obtain ⟨y', hy'⟩ := (key x⁻¹).1 hinv
    have hne : D.ntw.emb0 i x ≠ 0 := (map_ne_zero _).2 hx
    have hone : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) (y * y') = 1 := by
      rw [map_mul, hyx, hy', map_inv₀, mul_inv_cancel₀ hne]
    have hyy : y * y' = 1 := hinj (by rw [hone, map_one])
    have hu : IsUnit y := ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).1 hy hu
  · intro hpos
    obtain ⟨y, hy⟩ := (key x).1 hpos.le
    refine ⟨y, ?_, hy⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      have : y = 0 := hinj (by rw [hy, map_zero])
      exact not_isUnit_zero (this ▸ hu)
    have hinv : 0 ≤ D.what₂.places.val w ((x⁻¹ : D.LL0) : D.what₂.LL) := by
      refine (key x⁻¹).2 ⟨((hu.unit⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i), ?_⟩
      rw [map_inv₀, ← hy]
      exact (map_units_inv _ hu.unit).trans (by simp)
    have hsum := hmul x hx
    have : 0 < D.what₂.places.val w (x : D.what₂.LL) + D.what₂.places.val w ((x⁻¹ : D.LL0) : D.what₂.LL) :=
      add_pos_of_pos_of_nonneg hpos hinv
    rw [hsum] at this
    exact lt_irrefl _ this




open Classical in

def twInOf (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : TwIn D where
  E := E
  N0 := N0
  S i j b := if h : ∃ S, IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) S then h.choose else ∅

def twInRec (D : D7) (T : ThData D) (N0 : D.ntw.Tw → ℕ) : TwIn D := twInOf D (twEOf T) N0

def twInAll (D : D7) (N0 : D.ntw.Tw → ℕ) : TwIn D := twInOf D (IntegralHeckeForms.ExpDat.all D.nexp) N0








section Vac

variable (D : D7)












end Vac

end Formalism.L2

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain
open Formalism.L2.NT

namespace Formalism.L2

set_option synthInstance.maxHeartbeats 400000 in

structure NormalizedTwistCompatibility (D : D7) (C : NChoice D) (I : TwIn D) where

  gal : NGalTied D

  n : NormalizedHeckeDataPlaceholder D

  loc : LocTied D

  data : NormalizedDataCompatibility D

  cover : NormalizedLocalCompatibility D gal.mt

  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD

  rho : NR.NRhoTied D

  types : NormalizedTypesCompatibility D gal.fr.jE

  twF : TwFrame D
  tw : NTwTied D twF

  nct : NChTie D C

  exp : NExpTied D

  choice : NChoiceTied D C I (avDesign D)

  eMt_level : ∀ (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : TwistedAt D w) (hA : NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)))),
    ∃ ι : FractionRing (C.Oe w) →+* ℂ, (∀ x : D.what₂.LL, ι (C.embW w x) = D.what₂.embLL x) ∧
      (gal.mt (D.what₂.muTw w) j h1 h2).J =
        (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J ∧
      ∀ (κ : Formalism.AUTREP.GAf D.host.E D.R.nV) (h : κ ∈ (gal.mt (D.what₂.muTw w) j h1 h2).J)
        (h' : κ ∈ (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
          ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J),
        (((gal.mt (D.what₂.muTw w) j h1 h2).χ ⟨κ, h⟩ : ℂˣ) : ℂ) =
          ι (C.kMapE w (((exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
            ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).χ ⟨κ, h'⟩ : (NX.Kk D (C.twI w) (C.k' w))ˣ) :
              NX.Kk D (C.twI w) (C.k' w)))

  cf : Host.CharFrame D
  tp : Host.TupTied D cf C

  tupLink : gal.TupLink tp

  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  psi_eq : ∀ a x, (chiD.psi a).χ x = (tp.psi (D.nd.w a)).1 x

  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plκ : ∀ w, haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    IsLocalRing.ResidueField (plB w) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w)

  plB_loc : ∀ (i : D.nd.Loc) (y : D.nd.O i),
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ h : iotaOC D i y ∈ plB (D.nd.w i),
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (plκ (D.nd.w i) (IsLocalRing.residue (plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)

  plB_iota : ∀ (i : D.nd.Loc) k v x,
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    D.ntypes.iota k v (D.nd.w i) x = redThrough (plB (D.nd.w i)) (plκ (D.nd.w i)) (D.ntypes.teichC k x)

  etaT_link : ∀ (w : PlE D.host) (α : ℂ), chiD.etaT.At w α →
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹}

  muC_link : ∀ i : D.nd.Loc, ∀ᶠ w in Filter.cofinite, ∀ α : ℂ,
    (chiD.mu0 (D.nd.j i) * chiD.del (D.ntw.twOf i) * chiD.psi i).At w α →
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹}

  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)

  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y

end Formalism.L2
end
end
