import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidDefs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import BuildAid.D4
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthExistsCoatom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContraMapInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacing
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace PositivityTheory.Exh

section TensorExact

variable {G H V₁ V₂ V₃ W : Type} [Group G] [Group H] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂]
  [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] [AddCommGroup W] [Module ℂ W]
  {τ₁ : Representation ℂ G V₁} {τ₂ : Representation ℂ G V₂} {τ₃ : Representation ℂ G V₃}

theorem extL_exact (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃) (σ : Representation ℂ H W)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Injective (extL f σ) ∧ Function.Exact (extL f σ) (extL g σ) :=
  ⟨Module.Flat.rTensor_preserves_injective_linearMap (M := W) f.toLinearMap hf,
    Module.Flat.rTensor_exact W (f := f.toLinearMap) (g := g.toLinearMap) hfg⟩

theorem extR_exact (σ : Representation ℂ H W) (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Injective (extR σ f) ∧ Function.Exact (extR σ f) (extR σ g) :=
  ⟨Module.Flat.lTensor_preserves_injective_linearMap (M := W) f.toLinearMap hf,
    Module.Flat.lTensor_exact W (f := f.toLinearMap) (g := g.toLinearMap) hfg⟩

end TensorExact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section IndExact

variable {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]
  {ρ₁ : Representation ℂ (GL a k × GL b k) V₁} {ρ₂ : Representation ℂ (GL a k × GL b k) V₂}
  {ρ₃ : Representation ℂ (GL a k × GL b k) V₃}

theorem ind₂Map_exact (e : a ⊕ b ≃ n) (f : ρ₁.IntertwiningMap ρ₂) (g : ρ₂.IntertwiningMap ρ₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Injective (ind₂Map (k := k) e f) ∧ Function.Exact (ind₂Map (k := k) e f) (ind₂Map (k := k) e g) := by
  refine ⟨GlobalTheory.ParIndExact.parIndMap_injective _ _ hf, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · exact GlobalTheory.ParIndExact.parIndMap_exact _ (compMap f _) (compMap g _) hf
      (fun v hv => by obtain ⟨u, hu⟩ := (hfg v).1 hv; exact ⟨u, hu⟩) y hy
  · rintro ⟨u, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact hfg.apply_apply_eq_zero (u.1.1 x)

end IndExact

variable {nA nB m m' N : ℕ} {VA VB V₁ V₂ V₃ : Type} [AddCommGroup VA] [Module ℂ VA] [AddCommGroup VB] [Module ℂ VB]
  [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃]

set_option maxHeartbeats 1000000 in

theorem tripleProductMap_injective (h2 : m + nB = m') (h1 : nA + m' = N) (PA : Representation ℂ (GL (Fin nA) k) VA)
    (PB : Representation ℂ (GL (Fin nB) k) VB) {τ₁ : Representation ℂ (GL (Fin m) k) V₁}
    {τ₂ : Representation ℂ (GL (Fin m) k) V₂} {τ₃ : Representation ℂ (GL (Fin m) k) V₃}
    (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃) (hf : Function.Injective f)
    (hfg : Function.Exact f g) :
    Function.Injective (tripleProductMap h2 h1 PA PB f) ∧ Function.Exact (tripleProductMap h2 h1 PA PB f) (tripleProductMap h2 h1 PA PB g) := by
  have s1 := extL_exact (G := GL (Fin m) k) (H := GL (Fin nB) k) f g PB hf hfg
  have s2 := ind₂Map_exact (k := k) (stdSum h2) (extL f PB) (extL g PB) s1.1 s1.2
  have s3 := extR_exact (G := GL (Fin m') k) (H := GL (Fin nA) k) PA (ind₂Map (k := k) (stdSum h2) (extL f PB))
    (ind₂Map (k := k) (stdSum h2) (extL g PB)) s2.1 s2.2
  exact ind₂Map_exact (k := k) (stdSum h1) (extR PA (ind₂Map (k := k) (stdSum h2) (extL f PB)))
    (extR PA (ind₂Map (k := k) (stdSum h2) (extL g PB))) s3.1 s3.2

end PositivityTheory.Exh

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
open GlobalTheory.LocGL.ProjLine (quot quotMk)
open GlobalTheory.SegmentClass (rangeEquiv subIncl subIncl_injective)

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section General

variable {m N : ℕ}
  (T : ∀ {V : Type} [AddCommGroup V] [Module ℂ V], Representation ℂ (GL (Fin m) k) V → GlobalTheory.ProdFlatten.BR k N)
  (Tm : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (GL (Fin m) k) V}
    {τ' : Representation ℂ (GL (Fin m) k) W}, τ.IntertwiningMap τ' → (T τ).ρ.IntertwiningMap (T τ').ρ)
  (hT : ∀ {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    {τ₁ : Representation ℂ (GL (Fin m) k) V} {τ₂ : Representation ℂ (GL (Fin m) k) W} {τ₃ : Representation ℂ (GL (Fin m) k) U}
    (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃), Function.Injective f → Function.Exact f g →
      Function.Injective (Tm f) ∧ Function.Exact (Tm f) (Tm g))

def codSub {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) (S : Subrepresentation σ)
    (h : ∀ v, f v ∈ S.toSubmodule) : ρ.IntertwiningMap S.toRepresentation :=
  ⟨f.toLinearMap.codRestrict S.toSubmodule h, fun g => LinearMap.ext fun v => Subtype.ext (by
    change f (ρ g v) = σ g (f v)
    rw [f.isIntertwining])⟩

theorem codSub_injective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) (S : Subrepresentation σ)
    (h : ∀ v, f v ∈ S.toSubmodule) (hf : Function.Injective f) : Function.Injective (codSub f S h) :=
  fun a b hab => hf (congrArg Subtype.val hab)

include hT in

theorem mid_sub {V : Type} [AddCommGroup V] [Module ℂ V] {P : Representation ℂ (GL (Fin m) k) V}
    (hP : HasFiniteLength P) (hs : IsSmooth P) (x : IrrCl (GL (Fin N) k)) (S : Subrepresentation P)
    (hx : ∃ f : x.rep.ρ.IntertwiningMap (T S.toRepresentation).ρ, Function.Injective f) :
    ∃ c : IrrCl (GL (Fin m) k), IsSubquotient c.rep.ρ P ∧
      ∃ f : x.rep.ρ.IntertwiningMap (T c.rep.ρ).ρ, Function.Injective f := by
  have hInj : ∀ {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      {σ₁ : Representation ℂ (GL (Fin m) k) A} {σ₂ : Representation ℂ (GL (Fin m) k) B}
      (f : σ₁.IntertwiningMap σ₂), Function.Injective f → Function.Injective (Tm f) := by
    intro A B _ _ _ _ σ₁ σ₂ f hf
    refine (hT f (quotMk (Representation.IntertwiningMap.range σ₁ σ₂ f)) hf ?_).1
    intro y
    show (Representation.IntertwiningMap.range σ₁ σ₂ f).toSubmodule.mkQ y = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Representation.IntertwiningMap.mem_range σ₁ σ₂ f y
  have hzero : ∀ {A : Type} [AddCommGroup A] [Module ℂ A] {σ : Representation ℂ (GL (Fin m) k) A},
      Subsingleton A → Subsingleton (T σ).V := by
    intro A _ _ σ hA
    have h0inj : Function.Injective (0 : σ.IntertwiningMap σ) := fun a b _ => Subsingleton.elim a b
    have h0ex : Function.Exact (0 : σ.IntertwiningMap σ) (0 : σ.IntertwiningMap σ) := by
      intro y
      exact ⟨fun _ => ⟨y, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
    obtain ⟨hI, hE⟩ := hT (0 : σ.IntertwiningMap σ) (0 : σ.IntertwiningMap σ) h0inj h0ex
    have hz : ∀ z, Tm (0 : σ.IntertwiningMap σ) z = 0 := by
      intro z
      have h1 : Tm (0 : σ.IntertwiningMap σ) (Tm (0 : σ.IntertwiningMap σ) z) = 0 := (hE _).2 ⟨z, rfl⟩
      apply hI
      rw [h1, map_zero]
    refine ⟨fun a b => hI ?_⟩
    rw [hz a, hz b]
  have hwf := (hasFiniteLength_iff_wellFounded P).1 hP
  obtain ⟨S₀, hS₀, hmin⟩ := (@wellFounded_lt _ _ hwf.2).has_min
    {W : Subrepresentation P | ∃ f : x.rep.ρ.IntertwiningMap (T W.toRepresentation).ρ, Function.Injective f}
    ⟨S, hx⟩
  have hmin' : ∀ W : Subrepresentation P,
      (∃ f : x.rep.ρ.IntertwiningMap (T W.toRepresentation).ρ, Function.Injective f) → ¬ W < S₀ :=
    fun W hW => hmin W hW
  have hS₀' : ∃ f : x.rep.ρ.IntertwiningMap (T S₀.toRepresentation).ρ, Function.Injective f := hS₀
  obtain ⟨f₀, hf₀⟩ := hS₀'
  have hne : S₀ ≠ ⊥ := by
    intro h0
    subst h0
    haveI : Subsingleton (↥(⊥ : Subrepresentation P).toSubmodule) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : (a : V) = 0 := (Submodule.mem_bot ℂ).1 a.2
      have hb : (b : V) = 0 := (Submodule.mem_bot ℂ).1 b.2
      rw [ha, hb]
    haveI := hzero (σ := (⊥ : Subrepresentation P).toRepresentation) inferInstance
    haveI : Subsingleton x.rep.V := ⟨fun a b => hf₀ (Subsingleton.elim _ _)⟩
    haveI := x.rep.irr
    refine not_subsingleton (Subrepresentation x.rep.ρ) ⟨fun a b => Subrepresentation.ext (Submodule.ext fun v => ?_)⟩
    rw [Subsingleton.elim v 0]
    exact iff_of_true a.toSubmodule.zero_mem b.toSubmodule.zero_mem
  have hbot : ⊥ < S₀ := bot_lt_iff_ne_bot.2 hne
  obtain ⟨U, hU, hmax⟩ := (@wellFounded_gt _ _ hwf.1).has_min {W : Subrepresentation P | W < S₀} ⟨⊥, hbot⟩
  have hU' : U < S₀ := hU
  have hcov : U ⋖ S₀ := ⟨hU', fun W hUW hWS => hmax W hWS hUW⟩
  have hle : U.toSubmodule ≤ S₀.toSubmodule := hU'.le
  let ι : U.toRepresentation.IntertwiningMap S₀.toRepresentation :=
    ⟨Submodule.inclusion hle, fun g => LinearMap.ext fun v => Subtype.ext rfl⟩
  let p : S₀.toRepresentation.IntertwiningMap (subQuot S₀ U) :=
    ⟨(Submodule.comap S₀.toSubmodule.subtype U.toSubmodule).mkQ, fun g => LinearMap.ext fun v => rfl⟩
  have hιinj : Function.Injective ι := by
    intro a b h
    have h2 := congrArg (fun z : S₀.toSubmodule => (z : V)) h
    exact Subtype.ext h2
  have hex : Function.Exact ι p := by
    intro y
    show Submodule.Quotient.mk y = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    constructor
    · intro h
      exact ⟨⟨y, h⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact u.2
  obtain ⟨hTι, hTex⟩ := hT ι p hιinj hex
  let g := (Tm p).comp f₀
  rcases x.rep.irr.eq_bot_or_eq_top (Representation.IntertwiningMap.ker _ _ g) with hk | hk
  · have hginj : Function.Injective g := by
      intro a b hab
      have hmem : a - b ∈ Representation.IntertwiningMap.ker _ _ g := by
        rw [Representation.IntertwiningMap.mem_ker, map_sub, hab, sub_self]
      rw [hk] at hmem
      exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hmem)
    have hirr : (subQuot S₀ U).IsIrreducible := isIrreducible_subQuot hcov
    have hsm : IsSmooth (subQuot S₀ U) := (GlobalTheory.ParIndExact.isSubquotient_subQuot S₀ U).isSmooth hs
    let σ : IrrRep (GL (Fin m) k) := ⟨_, subQuot S₀ U, hsm, hirr⟩
    obtain ⟨e⟩ := IrrRep.nonempty_equiv_rep σ
    refine ⟨σ.cl, ?_, (Tm e.symm.toIntertwiningMap).comp g, ?_⟩
    · exact (IsSubquotient.of_injective e.toIntertwiningMap e.left_inv.injective).trans
        (GlobalTheory.ParIndExact.isSubquotient_subQuot S₀ U)
    · exact fun a b hab => hginj (hInj e.symm.toIntertwiningMap e.symm.left_inv.injective hab)
  · exfalso
    have hall : ∀ v, f₀ v ∈ (Representation.IntertwiningMap.range _ _ (Tm ι)).toSubmodule := by
      intro v
      have hv : v ∈ Representation.IntertwiningMap.ker _ _ g := by
        rw [hk]
        exact Submodule.mem_top
      rw [Representation.IntertwiningMap.mem_ker, Representation.IntertwiningMap.comp_apply] at hv
      exact (Representation.IntertwiningMap.mem_range _ _ _ _).2 ((hTex (f₀ v)).1 hv)
    have h1inj : Function.Injective (codSub f₀ _ hall) := codSub_injective f₀ _ hall hf₀
    let e := rangeEquiv (Tm ι) hTι
    exact hmin' U ⟨e.symm.toIntertwiningMap.comp (codSub f₀ _ hall),
      fun a b hab => h1inj (e.symm.left_inv.injective hab)⟩ hU'

include hT in

theorem mid_gen {V : Type} [AddCommGroup V] [Module ℂ V] {P : Representation ℂ (GL (Fin m) k) V}
    (hP : HasFiniteLength P) (hs : IsSmooth P) (x : IrrCl (GL (Fin N) k))
    (f : x.rep.ρ.IntertwiningMap (T P).ρ) (hf : Function.Injective f) :
    ∃ c : IrrCl (GL (Fin m) k), IsSubquotient c.rep.ρ P ∧
      ∃ f : x.rep.ρ.IntertwiningMap (T c.rep.ρ).ρ, Function.Injective f := by
  have hInj : ∀ {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      {σ₁ : Representation ℂ (GL (Fin m) k) A} {σ₂ : Representation ℂ (GL (Fin m) k) B}
      (f : σ₁.IntertwiningMap σ₂), Function.Injective f → Function.Injective (Tm f) := by
    intro A B _ _ _ _ σ₁ σ₂ f hf
    refine (hT f (quotMk (Representation.IntertwiningMap.range σ₁ σ₂ f)) hf ?_).1
    intro y
    show (Representation.IntertwiningMap.range σ₁ σ₂ f).toSubmodule.mkQ y = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Representation.IntertwiningMap.mem_range σ₁ σ₂ f y
  let j : P.IntertwiningMap (⊤ : Subrepresentation P).toRepresentation :=
    ⟨LinearMap.codRestrict (⊤ : Subrepresentation P).toSubmodule LinearMap.id (fun v => Submodule.mem_top),
      fun g => LinearMap.ext fun v => Subtype.ext rfl⟩
  have hj : Function.Injective j := fun a b h => congrArg Subtype.val h
  exact mid_sub T Tm hT hP hs x ⊤ ⟨(Tm j).comp f, fun a b h => hf (hInj j hj h)⟩

end General

end PositivityTheory.Exh

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdFlatten

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso in
theorem product_append_iso {p q r t : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t)
    (h : ∑ a, (Fin.append x y a).1 = r + t) : Iso (two rfl (pr x hx) (pr y hy)) (pr (Fin.append x y) h) :=
  GlobalTheory.T.product_irreducible_append_equiv k p q r t x y hx hy h

theorem pr_app {p q c r t N : ℕ} (x : Fin p → IrrGL k) (y : Fin q → IrrGL k) (z : Fin c → IrrGL k)
    (e : List.ofFn z = List.ofFn x ++ List.ofFn y) (hx : ∑ a, (x a).1 = r) (hy : ∑ a, (y a).1 = t) (hz : ∑ a, (z a).1 = N)
    (h : r + t = N) : Iso (pr z hz) (two h (pr x hx) (pr y hy)) := by
  subst h
  have h' : ∑ a, (Fin.append x y a).1 = r + t := by
    rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right, hx, hy]
  exact iso_trans (pr_congr (e.trans (List.ofFn_fin_append x y).symm) hz h') (iso_symm (product_append_iso x y hx hy h'))

theorem sum_get_eq' (L : List (IrrGL k)) : ∑ a, (L.get a).1 = (L.map fun x => x.1).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_get
  · simp
  · intro i h1 h2
    simp

theorem stage3_iso (A M B : List (IrrGL k)) {N nA nM nB m' : ℕ} (hd : ∑ a, ((A ++ M ++ B).get a).1 = N)
    (hA : ∑ a, (A.get a).1 = nA) (hM : ∑ a, (M.get a).1 = nM) (hB : ∑ a, (B.get a).1 = nB)
    (h2 : nM + nB = m') (h1 : nA + m' = N) :
    Iso (pr (A ++ M ++ B).get hd) (two h1 (pr A.get hA) (two h2 (pr M.get hM) (pr B.get hB))) := by
  have hMB : ∑ a, ((M ++ B).get a).1 = m' := by
    rw [sum_get_eq', List.map_append, List.sum_append, ← sum_get_eq', ← sum_get_eq', hM, hB, h2]
  exact iso_trans (pr_app A.get (M ++ B).get _ ((List.ofFn_get _).trans ((List.append_assoc A M B).trans (congrArg₂ _ (List.ofFn_get A).symm (List.ofFn_get (M ++ B)).symm))) hA hMB hd h1)
    (two_congr h1 (iso_refl _) (pr_app M.get B.get _ (by simp only [List.ofFn_get]) hM hB hMB h2))

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso in
theorem equiv_triple_product_of_iso {c a m b N nA nM nB m' : ℕ} (z : Fin c → IrrGL k) (A : Fin a → IrrGL k) (M : Fin m → IrrGL k) (B : Fin b → IrrGL k)
    (hd : ∑ a, (z a).1 = N) (hA : ∑ a, (A a).1 = nA) (hM : ∑ a, (M a).1 = nM) (hB : ∑ a, (B a).1 = nB)
    (h2 : nM + nB = m') (h1 : nA + m' = N) (H : Iso (pr z hd) (two h1 (pr A hA) (two h2 (pr M hM) (pr B hB)))) :
    Nonempty ((prodIrr z hd).Equiv (T3 h2 h1 (prodIrr A hA) (prodIrr B hB) (prodIrr M hM))) := H

end PositivityTheory.Exh

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdFlatten
open GlobalTheory.LocGL.ProjLine (quot quotMk)

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Emb {n : ℕ} (A C : BR k n) : Prop := ∃ f : A.ρ.IntertwiningMap C.ρ, Function.Injective f

def Sq {n : ℕ} (A C : BR k n) : Prop := IsSubquotient A.ρ C.ρ

def FL {n : ℕ} (A : BR k n) : Prop := HasFiniteLength A.ρ

theorem emb_trans {n : ℕ} {A C D : BR k n} (h : Emb A C) (h' : Emb C D) : Emb A D :=
  let ⟨f, hf⟩ := h; let ⟨g, hg⟩ := h'; ⟨g.comp f, hg.comp hf⟩

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem emb_of_iso {n : ℕ} {A C : BR k n} (h : Iso A C) : Emb A C :=
  let ⟨e⟩ := h; ⟨e.toIntertwiningMap, e.toLinearEquiv.injective⟩

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem embedding_middle_factor_triple {nA nB m m' N : ℕ} (h2 : m + nB = m') (h1 : nA + m' = N) (A : BR k nA) (B : BR k nB) {M M' : BR k m}
    (h : Emb M M') : Emb (two h1 A (two h2 M B)) (two h1 A (two h2 M' B)) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨tripleProductMap h2 h1 A.ρ B.ρ f, (tripleProductMap_injective h2 h1 A.ρ B.ρ f (quotMk f.range) hf fun y => ?_).1⟩
  show f.range.toSubmodule.mkQ y = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem mid_br {nA nB m m' : ℕ} (x : IrrGL k) (h2 : m + nB = m') (h1 : nA + m' = x.1) (A : BR k nA) (B : BR k nB) (M : BR k m)
    (hM : FL M) (hs : Sm M) (h : Emb (one x) (two h1 A (two h2 M B))) :
    ∃ c : IrrCl (GL (Fin m) k), Sq (one ⟨m, c⟩) M ∧ Emb (one x) (two h1 A (two h2 (one ⟨m, c⟩) B)) :=
  let ⟨f, hf⟩ := h
  mid_gen (fun τ => ⟨_, T3 h2 h1 A.ρ B.ρ τ⟩) (fun f => tripleProductMap h2 h1 A.ρ B.ρ f) (fun f g => tripleProductMap_injective h2 h1 A.ρ B.ρ f g) hM hs x.2 f hf

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem emb_pr_iff (x : IrrGL k) {a : ℕ} (z : Fin a → IrrGL k) (hd : ∑ i, (z i).1 = x.1) :
    Emb (one x) (pr z hd) ↔ ∃ f : x.rep.IntertwiningMap (prodIrr z hd), Function.Injective f := Iff.rfl

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem sq_pr_iff (x : IrrGL k) {a : ℕ} (z : Fin a → IrrGL k) (hd : ∑ i, (z i).1 = x.1) :
    Sq (one x) (pr z hd) ↔ IsSubquotient x.rep (prodIrr z hd) := Iff.rfl

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem fl_pr (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {a N : ℕ} (z : Fin a → IrrGL k) (hd : ∑ i, (z i).1 = N) : FL (pr z hd) :=
  GlobalTheory.T.product_irreducible_finite_length hA z hd

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem iso_one_pr (x : IrrGL k) (hd : ∑ _ : Fin 1, x.1 = x.1) : Iso (one x) (pr (fun _ : Fin 1 => x) hd) :=
  nonempty_equiv_prodIrr_one x hd

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem iso_pr_of {a b N : ℕ} (z : Fin a → IrrGL k) (w : Fin b → IrrGL k) (hz : ∑ i, (z i).1 = N) (hw : ∑ i, (w i).1 = N)
    (h : Nonempty ((prodIrr z hz).Equiv (prodIrr w hw))) : Iso (pr z hz) (pr w hw) := h

attribute [irreducible] Emb Sq FL

theorem embL_iff (x : IrrGL k) (l : List (IrrGL k)) : EmbL x l ↔ ∃ hd, Emb (one x) (pr l.get hd) :=
  exists_congr fun hd => (emb_pr_iff x l.get hd).symm

theorem deg3 (A M B : List (IrrGL k)) :
    ∑ a, ((A ++ M ++ B).get a).1 = ∑ a, (A.get a).1 + (∑ a, (M.get a).1 + ∑ a, (B.get a).1) := by
  simp only [sum_get_eq', List.map_append, List.sum_append, add_assoc]

theorem iso_single (σ : IrrGL k) (h : ∑ a, ([σ].get a).1 = σ.1) : Iso (one σ) (pr [σ].get h) :=
  iso_trans (iso_one_pr σ (by simp)) (pr_congr (by simp) _ h)

theorem embL_block {x : IrrGL k} {A M M' B : List (IrrGL k)} {m : ℕ} (hM : ∑ a, (M.get a).1 = m) (hM' : ∑ a, (M'.get a).1 = m)
    (h : Emb (pr M.get hM) (pr M'.get hM')) (hx : EmbL x (A ++ M ++ B)) : EmbL x (A ++ M' ++ B) := by
  obtain ⟨hd, e⟩ := (embL_iff _ _).1 hx
  have h1 : ∑ a, (A.get a).1 + (m + ∑ a, (B.get a).1) = x.1 := by rw [← hM, ← deg3, hd]
  have hd' : ∑ a, ((A ++ M' ++ B).get a).1 = x.1 := by rw [deg3, hM', h1]
  exact (embL_iff _ _).2 ⟨hd', emb_trans (emb_trans (emb_trans e (emb_of_iso (stage3_iso A M B hd rfl hM rfl rfl h1)))
    (embedding_middle_factor_triple rfl h1 _ _ h)) (emb_of_iso (iso_symm (stage3_iso A M' B hd' rfl hM' rfl rfl h1)))⟩

variable (k) in
theorem refineP' : RefineP k := fun x σ A M B hσ hx => by
  obtain ⟨hd, e⟩ := (embL_iff _ _).1 hσ
  have h : ∑ a, ([σ].get a).1 = σ.1 := by simp
  exact embL_block h hd (emb_trans (emb_of_iso (iso_symm (iso_single σ h))) e) hx

variable (k) in
theorem swapP' (h : GlobalTheory.BZSeg.LUnlinkedComm k) : SwapP k := fun x a b A B Δ Γ ha hb hl hx => by
  have hd : ∑ i, (![a, b] i).1 = a.1 + b.1 := by simp [Fin.sum_univ_two]
  have hd' : ∑ i, (![b, a] i).1 = a.1 + b.1 := by simp [Fin.sum_univ_two, add_comm]
  have h1 : ∑ i, ([a, b].get i).1 = a.1 + b.1 := by simp [sum_get_eq']
  have h2 : ∑ i, ([b, a].get i).1 = a.1 + b.1 := by simp [sum_get_eq', add_comm]
  exact embL_block h1 h2 (emb_of_iso (iso_trans (pr_congr (by simp [List.ofFn_succ]) h1 hd)
    (iso_trans (iso_pr_of _ _ hd hd' (h Δ Γ a b _ hd hd' hl ha hb)) (pr_congr (by simp [List.ofFn_succ]) hd' h2)))) hx

variable (k) in
theorem midP' (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) : MidP k := fun x A M B hx => by
  obtain ⟨hd, e⟩ := (embL_iff _ _).1 hx
  obtain ⟨m, hM⟩ : ∃ m, ∑ a, (M.get a).1 = m := ⟨_, rfl⟩
  have h1 : ∑ a, (A.get a).1 + (m + ∑ a, (B.get a).1) = x.1 := by rw [← hM, ← deg3, hd]
  obtain ⟨c, hc, e'⟩ := mid_br x rfl h1 _ _ _ (fl_pr hA M.get hM) (sm_pr M.get hM)
    (emb_trans e (emb_of_iso (stage3_iso A M B hd rfl hM rfl rfl h1)))
  have hs : ∑ a, ([(⟨m, c⟩ : IrrGL k)].get a).1 = m := by simp
  have hd' : ∑ a, ((A ++ [(⟨m, c⟩ : IrrGL k)] ++ B).get a).1 = x.1 := by rw [deg3, hs, h1]
  refine ⟨⟨m, c⟩, ⟨hM, (sq_pr_iff ⟨m, c⟩ M.get hM).1 hc⟩, (embL_iff _ _).2 ⟨hd', ?_⟩⟩
  exact emb_trans (emb_trans e' (embedding_middle_factor_triple rfl h1 _ _ (emb_of_iso (iso_single ⟨m, c⟩ hs))))
    (emb_of_iso (iso_symm (stage3_iso A [⟨m, c⟩] B hd' rfl hs rfl rfl h1)))

end PositivityTheory.Exh

end
end
