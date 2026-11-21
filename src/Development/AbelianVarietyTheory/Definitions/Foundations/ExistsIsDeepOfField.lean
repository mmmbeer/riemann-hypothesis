import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaExponentIdentities
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HalfLatticeTypes
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffTypeNormsPrincipal
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants Formalism.HN
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
open Formalism.L2.Pj hiding kap
open GlobalTheory.CompHt hiding rhoB

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P) {T : Par D} {j : ℕ} {l : Level T.H}
  {Xo : Moduli (T.Dw j) l} {c : Coeff l} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
  (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r)

abbrev gKap (T : Par D) (j : ℕ) : WTZ D.host.E := thetaExp D (T.Dw j) (kap D j)

abbrev gKapMinus (T : Par D) (j : ℕ) : WTZ D.host.E := thetaExp D (T.Dw j) (kapMinus D j)

abbrev gTw (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (twW D j)

abbrev gMinus (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uMinus D j)

abbrev gOne (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uOne Q j)

abbrev gTop (T : Par D) (j : ℕ) : WTZ D.host.E := plainExp D (T.Dw j) (uTop Q j)

abbrev nrmAt (G : WTZ D.host.E) : (c.F →+* ℂ) → cuspW Xo c U G → ℝ := normW U (xiR D) (fun _ => D.sp.W j) dict G

abbrev GoodAt (G : WTZ D.host.E) : Prop := GoodW U (xiR D) (fun _ => D.sp.W j) dict G

def refConst : ℝ := 1 / 2500

def ccOf : ℝ := (refSum U refConst (gOne Q T j)).toReal + aSum Q j + cInf Q j

theorem comp_nonempty (h : T.Pins) (hj : InR D j) : Nonempty (Comp Xo c) :=
  (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Xo c (by
    rw [(sig_eq h hj).2.2]
    have := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega)).1

variable [StarRing c.F] (h : T.Pins) (hj : InR D j) (CI C2 : ℝ) (Vs : ValFam Xo c) (Hb : Type) [Fintype Hb]
  (NN : Submodule (𝓞 c.F) (cuspW Xo c U (gKap T j)))
  (Ph : cuspW Xo c U (gKapMinus T j) →ₗ[c.F] (Hb → cuspW Xo c U (gKap T j)))
  (e : cuspW Xo c U (gKap T j) →ₗ[c.F] cuspW Xo c U (gKap T j)) (g : ℕ)

def facWith : SlopeBoundLiftData c.F (pageOf Q) where
  w τ := wAn D j τ
  w0 τ := wj D j τ
  c1 τ := GlobalTheory.FlatLine.c1 U (xiR D) (psiOf h.1 τ)
  ua τ := nrm D (uAn D j τ)
  kap := nKap D j
  q' := qq D j
  pq := (pp D j : ℝ) - qq D j
  ι := Comp Xo c
  fι := haveI := CompFin.finite_comp Xo c; Fintype.ofFinite _
  nι := comp_nonempty h hj
  DY := dY D
  A := cA Q j
  cs := cStarInf U (xiR D) (fun _ => D.sp.W j) dict (gOne Q T j)
  X := CI * placeRankTwoOne.LL0 D L * nPrW Q j
  cc := ccOf Q U
  E0 := eZero D j
  Qcc := (numAt Q j).Qc
  ρ := rhoB Q j
  R1 := rOne Q C2 j
  R2 := rTwo Q j
  Bn := ((tN Q - 1).choose (placeRankTwoOne.dimY D) : ℕ)
  δ' := compMean fun Z => delPrime U Z (toWt (T.Dw j) (uOne Q j))
  h Z := compHeight U (xiR D) (fun _ => D.sp.W j) dict Z (gOne Q T j)
  sl Z := (compVolSlope U (xiR D) 8 Vs Z (toWt (T.Dw j) (uPr Q j))).toReal
  δc Z := compDeg U Z (gOne Q T j)
  dc Z := rankOn U Z (gTop Q T j)
  degc Z := degOn U (xiR D) (fun _ => D.sp.W j) dict Z (gTop Q T j)
  PPf := (numAt Q j).Pfl
  mv := shift D
  muU := slopeW_sq U (xiR D) (fun _ => D.sp.W j) dict (gMinus T j)
  nA := cDim (nrmAt U dict (gKapMinus T j))
  nB := cDim (piNorm Hb (nrmAt U dict (gKap T j)))
  nN := cDim (nrmAt U dict (gKap T j))
  XA := frameCo _
  XB := frameCo _
  XN := frameCo _
  LA := latCo _ (latW U (gKapMinus T j))
  LB := latCo _ (piLat Hb NN)
  NN := latCo _ NN
  Mk := latCo _ (latW U (gKap T j))
  φ := mapCo _ _ Ph
  e := mapCo _ _ e
  g := g
  PPh := 3 / 2 * Real.log (Fintype.card Hb) + (numAt Q j).U0
  abelian₂ := lamKap Q j + Real.log (Fintype.card Hb)
  δ := del D
  o' := GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.ringCost c.F
  n2 := measureMove D L

local notation "𝐅" => facWith Q U dict h hj CI C2 Vs Hb NN Ph e g













variable {U dict}









example (hF : GlobalTheory.FlatLine.FlatDegree U (xiR D) L.logOm) (τ : D.what₂.Tau) :
    (𝐅).c1 τ = -GlobalTheory.FlatLine.flatDegVal (T.Dw j) L.logOm :=
  GlobalTheory.FlatLine.FlatExistsAt.c1_eq hF (comp_nonempty h hj) _

end GlobalTheory.SlopeRec
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj hiding kap
open GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.JoinChr Formalism.L2.Host in
set_option maxHeartbeats 1000000 in

theorem exists_unif {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) {l : Level T.Q.H} (hA : l.A = 1)
    (Xo : Moduli (T.Q.Dw j) l) (c : Coeff l) :
    ∃ (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
      (∀ σ, GoodEmb c σ → GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt (U σ) (D.sp.W j) (dict σ) (T.iota j)) ∧
      ∀ σ, GoodEmb c σ → ∀ k la, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ la γ = 1 := by
  have hpos := GlobalTheory.CovTop.Inhab.rank_pos T.toCore hT.pins j hj
  have hW : (D.sp.W j).rank = D.R.r := D.sp.W_rank j hj.1 hj.2
  have hι := (GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj _ T.good_σ₀ _ (hT.spaceW j hj _ T.good_σ₀) hW).1
  obtain ⟨Kf, hKf⟩ := (GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds D (D.sp.W j) l.M).1
  have hpk : ∀ σ, GoodEmb c σ → ∃ (U : Unf Xo c σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r),
      GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt U (D.sp.W j) dict (T.iota j) ∧ ∀ k la γ, (U.X k).χ la γ = 1 := fun σ hσ => by
    obtain ⟨C, hC, hCι⟩ := (GlobalTheory.Member.exists_ctx D _ _ _ Xo c σ (D.sp.W j) D.R.r hW _ hι hpos hA hσ).1
    obtain ⟨un, dict, mu, -, -, hP⟩ := GlobalTheory.Member.exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1
      ⟨continuous_const, fun _ => rfl⟩ (fun _ => rfl)
    rw [hCι] at hP
    obtain ⟨g, e, F, ik, φ, th, b1, b2, b3⟩ := hP.dictLaws
    exact ⟨C.unf un, dict, ⟨hP.unf, hW, Kf, th, C.x₀, g, e, F, ik, φ, hP.modelW, hP.familyUniformisationBasePointOrthogonal, hKf, b1, b2, hι.emb,
      ⟨1, fun x y => by simpa using hι.isom x y⟩, b3⟩, hP.chi1⟩
  have hall : ∀ σ, ∃ (U : Unf Xo c σ D.R.r) (dict : GA D (D.sp.W j) → Σ k, Frame (U.X k).Ψ D.R.r), GoodEmb c σ →
      GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt U (D.sp.W j) dict (T.iota j) ∧ ∀ k la γ, (U.X k).χ la γ = 1 := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨U, dict, h⟩ := hpk σ hσ
      exact ⟨U, dict, fun _ => h⟩
    · obtain ⟨U, dict, -⟩ := hpk c.F.val.toRingHom rfl
      obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.abelianSchemeLaws_all.2.secTwist _ _ _ _
        Xo c hpos σ
      exact ⟨{ Comp := Unit, X := fun _ => U.X (dict 1).1, un := fun _ _ => y }, fun _ => ⟨(), fun _ => 0⟩,
        fun h => absurd h hσ⟩
  choose U dict hP using hall
  exact ⟨U, dict, fun σ hσ => (hP σ hσ).1, fun σ hσ k la γ _ => (hP σ hσ).2 k la γ⟩

theorem exists_deepLevel (L : SizeData₂ D) {Q : Par D} (hQ : Q.Pins) (h5 : 5 ≤ D.host.splitBound)
    (h15 : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)) :
    ∃ l : Level Q.H, (l.M = levDeep D L ∧ l.A = 1 ∧ Q.l.Dvd l) ∧ IsTypeLevel l := by
  obtain ⟨s, hs⟩ := GlobalTheory.CovTop.Inhab.exists_root h5
  obtain ⟨I, hK, hp, hI⟩ := GlobalTheory.CovTop.Inhab.exists_half Q.H s (by rw [hQ.1.1]; exact hs) (expC D L)
  obtain ⟨l, l1, l2, -, -, -, l6⟩ := GlobalTheory.CoverHalf.exists_coverLevel Q.l hQ.2.1.2 (15 ^ expC D L) I (Odd.pow (by decide))
    (by rw [hQ.2.1.1]; exact h15.pow_left _) hK hp hI
  rw [hQ.2.1.1] at l2
  exact ⟨l, ⟨by rw [l2, levDeep, ← mul_pow]; norm_num, l6, l1⟩,
    (isTypeLevel_of_eq l6 l2 (h15.symm.pow_right _)).1⟩

theorem exists_deepField (T : CoreJ D) {j : ℕ} (hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q) {l : Level T.Q.H}
    (Xo : Moduli (T.Q.Dw j) l) {n : ℕ} (hn : n ≠ 0) :
    ∃ (c : Coeff l) (le : T.Q.c.F ≤ c.F),
      (letI := (GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.incl (T := T) le).toAlgebra; IsGalois T.Q.c.F c.F) ∧ FnAlgClosed Xo c ∧
        KPsiIn (Dw := T.Q.Dw j) c ∧ ∃ ζ : c.F, IsPrimitiveRoot ζ n := by
  have hζ := Complex.isPrimitiveRoot_exp n hn
  haveI := T.Q.c.fin
  haveI := IntermediateField.adjoin.finiteDimensional (K := ℚ) (hζ.isIntegral (Nat.pos_of_ne_zero hn)).tower_top
  obtain ⟨c₀, h₀⟩ := GlobalTheory.TupleCover.exists_coeff_ge l
    (T.Q.c.F ⊔ IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / n)})
  obtain ⟨c₁, h₁, hc₁⟩ := (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Xo c₀ hpos).2
  obtain ⟨c₂, h₂, hc₂⟩ := GlobalTheory.exists_coeff_typeNorms_principal _ _ (T.Q.Dw j) l c₁
  haveI := c₂.fin
  let N : IntermediateField ℚ ℂ := IntermediateField.normalClosure ℚ c₂.F ℂ
  have hN : c₂.F ≤ N := IntermediateField.le_normalClosure c₂.F
  let c : Coeff l := ⟨N, inferInstance, fun τ a => hN (c₂.conj τ a), hN c₂.zeta_mem, c₂.le.trans hN⟩
  have h0 : c₀.F ≤ N := h₁.trans (h₂.trans hN)
  have le : T.Q.c.F ≤ c.F := le_sup_left.trans (h₀.trans h0)
  refine ⟨c, le, ?_, hc₁ c (h₂.trans hN), hc₂ c hN,
    ⟨_, h0 (h₀ (le_sup_right (a := T.Q.c.F) (IntermediateField.mem_adjoin_simple_self ℚ _)))⟩, ?_⟩
  · letI := (GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.incl (T := T) le).toAlgebra
    haveI : IsScalarTower ℚ T.Q.c.F c.F := IsScalarTower.of_algebraMap_eq fun x => by simp
    haveI : Normal ℚ c.F := by
      haveI : Algebra.IsAlgebraic ℚ c₂.F := inferInstance
      exact (Algebra.IsAlgebraic.isNormalClosure_normalClosure (F := ℚ) (K := c₂.F) (L := ℂ)
        fun x => IsAlgClosed.splits _).normal
    haveI : IsGalois ℚ c.F := ⟨⟩
    exact IsGalois.tower_top_of_isGalois ℚ T.Q.c.F c.F
  · exact IsPrimitiveRoot.of_map_of_injective (f := c.F.val) hζ c.F.val.injective

theorem exists_chars_prime {K : Type} [Field K] {g : ℕ} [Fact g.Prime] {ζ : K} (h : IsPrimitiveRoot ζ (g * (g - 1))) :
    (∃ ψ : AddChar (ZMod g) K, ψ ≠ 1) ∧ ∃ om : (ZMod g)ˣ →* Kˣ, Function.Injective om := by
  have hg : g.Prime := Fact.out
  have h1 : 0 < g - 1 := Nat.sub_pos_of_lt hg.one_lt
  have hp := Nat.mul_pos hg.pos h1
  constructor
  · have hz : IsPrimitiveRoot (ζ ^ (g - 1)) g := h.pow hp (mul_comm _ _)
    refine ⟨AddChar.zmodChar g hz.pow_eq_one, fun e => ?_⟩
    have := DFunLike.congr_fun e ((1 : ℕ) : ZMod g)
    rw [AddChar.zmodChar_apply', pow_one, AddChar.one_apply] at this
    exact hz.ne_one hg.one_lt this
  · have hz : IsPrimitiveRoot (ζ ^ g) (g - 1) := h.pow hp rfl
    have hu := hz.isUnit_unit h1.ne'
    have hc : Nat.card (ZMod g)ˣ = Nat.card (Subgroup.zpowers (hz.isUnit h1.ne').unit) := by
      rw [Nat.card_zpowers, ← hu.eq_orderOf, Nat.card_eq_fintype_card, ZMod.card_units]
    exact ⟨(Subgroup.subtype _).comp (mulEquivOfCyclicCardEq hc).toMonoidHom,
      Subtype.val_injective.comp (mulEquivOfCyclicCardEq hc).injective⟩

theorem exists_chars {K : Type} [Field K] {ζ : K} (h : IsPrimitiveRoot ζ (∏ k, D.host.g k * (D.host.g k - 1))) :
    (∃ ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) K, IsGenericFamily ψ) ∧
      ∃ om : ∀ k : Fin 2, (ZMod (D.host.g k))ˣ →* Kˣ, IsGeneratorFamily om := by
  have hk : ∀ k : Fin 2, (∃ ψ : AddChar (ZMod (D.host.g k)) K, ψ ≠ 1) ∧
      ∃ om : (ZMod (D.host.g k))ˣ →* Kˣ, Function.Injective om := fun k => by
    obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem (fun k => D.host.g k * (D.host.g k - 1)) (Finset.mem_univ k)
    exact exists_chars_prime (h.pow (Finset.prod_pos fun k _ => Nat.mul_pos (D.host.g_prime k).pos
      (Nat.sub_pos_of_lt (D.host.g_prime k).one_lt)) (ha.trans (mul_comm _ _)))
  choose ψ hψ using fun k => (hk k).1
  choose om hom using fun k => (hk k).2
  exact ⟨⟨fun v => ψ v.1, fun v => hψ v.1⟩, om, hom⟩

end GlobalTheory.SlopeRec
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField Finset Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants Formalism.HN
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
open Formalism.L2.Pj hiding kap
open GlobalTheory.CompHt hiding rhoB
open GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

section Deep

variable (T : CoreJ D) (j : ℕ) {l : Level T.Q.H} (Xo : Moduli (T.Q.Dw j) l) (c : Coeff l)
  (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r)

structure IsDeep : Prop where
  level : l.M = levDeep D L ∧ l.A = 1 ∧ T.Q.l.Dvd l
  le : T.Q.c.F ≤ c.F
  galois : letI := (GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.incl (T := T) le).toAlgebra; IsGalois T.Q.c.F c.F
  geo : FnAlgClosed Xo c
  typeNorm : KPsiIn (Dw := T.Q.Dw j) c
  size : Real.log (Module.finrank ℚ c.F) ≤ (numAt Q j).dP ∧ Real.log (rootDiscr c.F) ≤ (numAt Q j).rP
  unif : ∀ σ, GoodEmb c σ → GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt (U σ) (D.sp.W j) (dict σ) (T.iota j)
  chi : ∀ σ, GoodEmb c σ → ∀ k la, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ la γ = 1

variable (L) in

structure IsDeepLevel : Prop where
  level : l.M = levDeep D L ∧ l.A = 1 ∧ T.Q.l.Dvd l
  le : T.Q.c.F ≤ c.F
  galois : letI := (GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.incl (T := T) le).toAlgebra; IsGalois T.Q.c.F c.F
  geo : FnAlgClosed Xo c
  typeNorm : KPsiIn (Dw := T.Q.Dw j) c
  unif : ∀ σ, GoodEmb c σ → GlobalTheory.IndefiniteRowSideFullHecke.HalfLatticeTypes.IsUnifAt (U σ) (D.sp.W j) (dict σ) (T.iota j)
  chi : ∀ σ, GoodEmb c σ → ∀ k la, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ la γ = 1

variable {T j} in

theorem exists_isDeepLevel (L : SizeData₂ D) (hT : LawsJ T) (hj : InR D j) (h5 : 5 ≤ D.host.splitBound)
    (h15 : Nat.Coprime 15 (D.host.g 0 * D.host.g 1)) {n : ℕ} (hn : n ≠ 0) :
    ∃ (l : Level T.Q.H) (Xo : Moduli (T.Q.Dw j) l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
      IsDeepLevel L T j Xo c U dict ∧ IsTypeLevel l ∧ ∃ ζ : c.F, IsPrimitiveRoot ζ n := by
  have hpos := GlobalTheory.CovTop.Inhab.rank_pos T.toCore hT.pins j hj
  obtain ⟨l, hl, ht⟩ := exists_deepLevel L hT.pins h5 h15
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ _ (T.Q.Dw j) l hpos
  obtain ⟨c, le, h1, h2, h3, h4⟩ := exists_deepField T hpos Xo hn
  obtain ⟨U, dict, h6, h7⟩ := exists_unif hT hj hl.2.1 Xo c
  exact ⟨l, Xo, c, U, dict, ⟨hl, le, h1, h2, h3, h6, h7⟩, ht, h4⟩

variable {Q T j Xo c U dict}





end Deep

section Restrict

variable {K M M' : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M']

open Classical in

def restrictOr (φ : M →ₗ[K] M') (C : Submodule K M) (C' : Submodule K M') : C →ₗ[K] C' :=
  if h : ∀ x ∈ C, φ x ∈ C' then φ.restrict h else 0


end Restrict

section Keeps

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem mul_mem_cuspW {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) {f g : Rul Xo c} (hf : f ∈ cuspW Xo c U G)
    (hg : g ∈ cuspW Xo c U G') : f * g ∈ cuspW Xo c U (G + G') := by
  rw [mem_cuspW] at hf hg ⊢
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [show exZ Dw (G + G') = exZ Dw G + exZ Dw G' from funext fun i => exZ_add _ _ _]
    exact mul_mem_secZ hf.1 hg.1
  · rw [AllWt.rdU_mul, show modelWt (U σ) (G + G') = fun k => modelWt (U σ) G k + modelWt (U σ) G' k from
      funext (modelWt_add (U σ) hG hG')]
    exact holSub_mul siegelSpaceAlgebra_holds (hf.2 σ hσ) (hg.2 σ hσ)

theorem levPh_mem_cuspW {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) (hK : KeepsCusp U (G + G'))
    (hK' : KeepsCusp U G') {S : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut Dw l)} (χ : S →* (c.F)ˣ) {u f : Rul Xo c}
    (hu : u ∈ cuspW Xo c U G') (hf : f ∈ cuspW Xo c U G) (h : S) : levPh Xo c S χ u f h ∈ cuspW Xo c U (G + G') := by
  rw [levPh_apply, levTr_apply]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hK _ _ (mul_mem_cuspW hG hG' hf (hK' _ _ hu)))

variable (U) in

def IsMultiplier (x : ℝ) (S : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut Dw l)) (G : WTZ E) (B : ℝ) (u : cuspW Xo c U G) : Prop :=
  u ∈ latW U G ∧ (∀ Z : Comp Xo c, genVal Z (levDet Xo c S u) ≠ 0) ∧
    ∀ σ, GoodEmb c σ → ∀ z : Σ k, Frame ((U σ).X k).Ψ r, z.2 ∈ ((U σ).X z.1).dom → homN (U σ) x G u z ≤ Real.exp B

end Keeps


set_option genInjectivity false in
set_option genSizeOfSpec false in

structure LiftData (T : CoreJ D) (i : Fin D.R.m) : Type 1 where

  l : Level T.Q.H
  typeLevel : IsTypeLevel l

  Xo : Moduli (T.Q.Dw ((i : ℕ) + 1)) l

  c : Coeff l

  U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r

  dict : ∀ σ, GA D (D.sp.W ((i : ℕ) + 1)) → Σ k, Frame ((U σ).X k).Ψ D.R.r

  fr : TypeFrame (T.Q.Dw ((i : ℕ) + 1)) l

  ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) c.F

  om : ∀ k : Fin 2, (ZMod (D.host.g k))ˣ →* (c.F)ˣ

  u₀ : cuspW Xo c U (gTw T.Q ((i : ℕ) + 1))

theorem inR_succ (i : Fin D.R.m) : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

namespace LiftData

variable {T : CoreJ D} {i : Fin D.R.m} (Y : LiftData T i)

abbrev Hb : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelAut (T.Q.Dw ((i : ℕ) + 1)) Y.l) := grpHR Y.fr

abbrev V (G : WTZ D.host.E) : Submodule Y.c.F (Rul Y.Xo Y.c) := cuspW Y.Xo Y.c Y.U G

def NN : Submodule (𝓞 Y.c.F) (Y.V (gKap T.Q ((i : ℕ) + 1))) := latN Y.fr Y.U _ Y.ψ

def Ph : Y.V (gKapMinus T.Q ((i : ℕ) + 1)) →ₗ[Y.c.F] (Y.Hb → Y.V (gKap T.Q ((i : ℕ) + 1))) :=
  LinearMap.pi fun h => restrictOr (LinearMap.proj h ∘ₗ levPh Y.Xo Y.c Y.Hb (chiHR Y.fr Y.ψ) Y.u₀) _ _

def eGood : Y.V (gKap T.Q ((i : ℕ) + 1)) →ₗ[Y.c.F] Y.V (gKap T.Q ((i : ℕ) + 1)) :=
  restrictOr (goodOp Y.Xo Y.c Y.typeLevel Y.fr Y.om i) _ _

structure Good : Prop where
  deep : IsDeep Q T ((i : ℕ) + 1) Y.Xo Y.c Y.U Y.dict
  roots : HasLevelRoots D.host T.Q.c.F
  generic : IsGenericFamily Y.ψ
  generator : IsGeneratorFamily Y.om
  mult : (i : ℕ) + 1 < D.R.m →
    IsMultiplier Y.U (xiR D) Y.Hb (gTw T.Q ((i : ℕ) + 1)) (numAt Q ((i : ℕ) + 1)).U0 Y.u₀



variable (h : T.Q.Pins) (hK : KeepsCusp Y.U (gKap T.Q ((i : ℕ) + 1))) (he : IsIdempotentElem (goodIdemTw Y.om i))
include h hK he



end LiftData

variable {T : CoreJ D} (h : T.Q.Pins) {i : Fin D.R.m} (Y : LiftData T i) [StarRing Y.c.F] (CI C2 : ℝ)

def facOf : SlopeBoundLiftData Y.c.F (pageOf Q) :=
  facWith Q Y.U Y.dict h (inR_succ i) CI C2 (mixVals Y.Xo Y.c (bZero Q ((i : ℕ) + 1))) Y.Hb Y.NN Y.Ph Y.eGood
    (Nat.card (LevelGroup D.host))








open Classical in

def LiftData.ofCore (hT : LawsJ T) (i : Fin D.R.m) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) T.Q.c.F)
    (om : ∀ k : Fin 2, (ZMod (D.host.g k))ˣ →* (T.Q.c.F)ˣ)
    (u₀ : cuspW (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (gTw T.Q ((i : ℕ) + 1))) : LiftData T i where
  l := T.Q.l
  typeLevel := (isTypeLevel_of_pin hT.pins.2.1).1
  Xo := T.Q.Xo _
  c := T.Q.c
  U := T.U _
  dict σ g := if hσ : GoodEmb T.Q.c σ then T.dict _ σ (cast (congrArg (GA D) (hT.spaceW _ (inR_succ i) σ hσ)).symm g)
    else T.dict _ σ 1
  fr := ((isTypeLevel_of_pin hT.pins.2.1).1.nonempty_typeFrame (sig_eq hT.pins (inR_succ i)).2.2).some
  ψ := ψ
  om := om
  u₀ := u₀



example (hT : LawsJ T) (hκ : DV.KapDef D) (i : Fin D.R.m) (ψ om u₀) :
    (LiftData.ofCore hT i ψ om u₀).V (gKap T.Q ((i : ℕ) + 1)) =
      T.cuspA ((i : ℕ) + 1) (wtA (Formalism.IndefR.FWT.kapTop D i)) (Formalism.IndefR.FWT.kapTop D i).n := by
  rw [gKap, thetaExp_kap_kapTop hT.pins hκ]
  exact cuspW_wtZ _ _

example (hrd : 1 ≤ D.host.rdE) : 0 ≤ (facOf Q h Y CI C2).mv := by
  have h1 : 0 ≤ lrd D := Real.log_nonneg hrd
  have h2 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  show 0 ≤ shift D
  unfold shift
  positivity

end GlobalTheory.SlopeRec
end
end
