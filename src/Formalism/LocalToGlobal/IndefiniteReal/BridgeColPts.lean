import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
import Formalism.LocalToGlobal.Columns.RowFormsAdelic

section
open NumberField

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2.DIV Formalism.L2.Col

structure AdPts {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) {G Γ : Type} [Group G] [Group Γ]
    (ι : Γ →* G) (J : Subgroup G) where
  K1 : Subgroup G
  principal_congruence_le : K1 ≤ J
  q : G → S.D
  gl : Γ × J →* S.G
  gl_surj : Function.Surjective gl
  gl_ker : ∀ (γ : Γ) (k : J), gl (γ, k) = 1 ↔ γ = 1 ∧ (k : G) ∈ K1
  q_surj : Function.Surjective q
  q_eqv : ∀ (γ : Γ) (k : J) (x : G), q (ι γ * x * (k : G)⁻¹) = gl (γ, k) • q x
  q_fib : ∀ x x' : G, q x = q x' ↔ ∃ k1 ∈ K1, x' = x * k1

section Stab

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {J : Subgroup G}

def stabJ {y : G} (γ : stab ι J y) : J := ⟨y⁻¹ * ι (γ : Γ) * y, (mem_stab ι).1 γ.2⟩

theorem stabK_eq_inv {y : G} (γ : stab ι J y) : stabK ι γ = (stabJ γ)⁻¹ := rfl

def stabHom (y : G) : stab ι J y →* Γ × J where
  toFun γ := ((γ : Γ), stabJ γ)
  map_one' := Prod.ext rfl (Subtype.ext (by simp [stabJ]))
  map_mul' a b := Prod.ext rfl (Subtype.ext (by
    show y⁻¹ * ι ((a : Γ) * (b : Γ)) * y = (y⁻¹ * ι (a : Γ) * y) * (y⁻¹ * ι (b : Γ) * y)
    rw [map_mul]; group))

end Stab

namespace AdPts

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G} (A : AdPts S ι J)

theorem q_mul (γ : Γ) (x : G) (k : J) : A.q (ι γ * x * (k : G)) = A.gl (γ, k⁻¹) • A.q x := by
  have h := A.q_eqv γ k⁻¹ x
  simpa using h

def y (c : S.Cl) : G := Function.surjInv A.q_surj (S.outSec.rep c)

theorem q_y (c : S.Cl) : A.q (A.y c) = S.outSec.rep c := Function.surjInv_eq A.q_surj _

theorem isReps : IsReps ι J A.y := by
  intro h
  refine ⟨S.cls (A.q h), ?_, ?_⟩
  · obtain ⟨g, hg⟩ := S.outSec.exists_mv (A.q h)
    obtain ⟨⟨γ, k⟩, rfl⟩ := A.gl_surj g
    rw [← A.q_y, ← A.q_eqv] at hg
    obtain ⟨k1, hk1, e⟩ := (A.q_fib _ _).1 hg
    refine ⟨γ, k⁻¹ * ⟨k1, A.principal_congruence_le hk1⟩, e.trans ?_⟩
    simp [mul_assoc]
  · rintro c ⟨γ, k, rfl⟩
    rw [A.q_mul, S.cls_smul, A.q_y, S.outSec.spec]

def toStab (c : S.Cl) : stab ι J (A.y c) →* MulAction.stabilizer S.G (S.outSec.rep c) :=
  (A.gl.comp (stabHom (A.y c))).codRestrict _ (fun γ => by
    rw [MulAction.mem_stabilizer_iff]
    show A.gl ((γ : Γ), stabJ γ) • S.outSec.rep c = S.outSec.rep c
    rw [← A.q_y, ← A.q_eqv]
    congr 1
    show ι (γ : Γ) * A.y c * ((A.y c)⁻¹ * ι (γ : Γ) * A.y c)⁻¹ = A.y c
    group)

theorem toStab_coe (c : S.Cl) (γ : stab ι J (A.y c)) :
    ((A.toStab c γ : MulAction.stabilizer S.G (S.outSec.rep c)) : S.G) = A.gl ((γ : Γ), stabJ γ) := rfl

theorem toStab_bij (c : S.Cl) : Function.Bijective (A.toStab c) := by
  constructor
  · refine (injective_iff_map_eq_one _).2 fun γ hγ => ?_
    have h1 : A.gl ((γ : Γ), stabJ γ) = 1 := by
      rw [← A.toStab_coe, hγ]
      rfl
    exact Subtype.ext ((A.gl_ker _ _).1 h1).1
  · intro g
    obtain ⟨⟨γ, k⟩, hg⟩ := A.gl_surj g
    have hfix : A.gl (γ, k) • S.outSec.rep c = S.outSec.rep c := by
      rw [hg]
      exact g.2
    rw [← A.q_y, ← A.q_eqv] at hfix
    obtain ⟨k1, hk1, e⟩ := (A.q_fib _ _).1 hfix.symm
    have hmem : (A.y c)⁻¹ * ι γ * A.y c = k1 * (k : G) := by
      calc (A.y c)⁻¹ * ι γ * A.y c = (A.y c)⁻¹ * (ι γ * A.y c * (k : G)⁻¹) * k := by group
        _ = k1 * (k : G) := by rw [e]; group
    have hs : γ ∈ stab ι J (A.y c) := by
      rw [mem_stab, hmem]
      exact J.mul_mem (A.principal_congruence_le hk1) k.2
    refine ⟨⟨γ, hs⟩, Subtype.ext ?_⟩
    rw [toStab_coe, ← hg]
    have hJ : (stabJ (⟨γ, hs⟩ : stab ι J (A.y c)) : J) = ⟨k1, A.principal_congruence_le hk1⟩ * k := Subtype.ext hmem
    have h1 : A.gl ((1 : Γ), (⟨k1, A.principal_congruence_le hk1⟩ : J)) = 1 := (A.gl_ker _ _).2 ⟨rfl, hk1⟩
    have e2 : ((γ, stabJ (⟨γ, hs⟩ : stab ι J (A.y c))) : Γ × J) = ((1 : Γ), (⟨k1, A.principal_congruence_le hk1⟩ : J)) * (γ, k) := by
      rw [hJ]
      exact Prod.ext (one_mul γ).symm rfl
    rw [e2, map_mul, h1, one_mul]

def stabEquiv (c : S.Cl) : stab ι J (A.y c) ≃* MulAction.stabilizer S.G (S.outSec.rep c) :=
  MulEquiv.ofBijective (A.toStab c) (A.toStab_bij c)

end AdPts

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def classPresOf {S : GSD K} {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {J : Subgroup G} (A : AdPts S ι J) (h : S.Ok)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (_hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v)) :
    ClassPres ι (S.toCSD h) σ ρ J χ where
  y := A.y
  reps := A.isReps
  stabI c := (A.stabEquiv c).symm
  coef := coef
  coef_li := hli
  coef_span := hspan
  coef_pair := hpair
  coef_act := by
    intro c g x
    obtain ⟨γ, rfl⟩ := (A.stabEquiv c).surjective g
    show coef (S.ρ ((A.stabEquiv c γ : MulAction.stabilizer S.G (S.outSec.rep c)) : S.G) x) =
      (χ (stabK ι ((A.stabEquiv c).symm (A.stabEquiv c γ))) : ℂ) • ρ (((A.stabEquiv c).symm (A.stabEquiv c γ)) : Γ) (coef x)
    rw [MulEquiv.symm_apply_apply]
    have e1 : ((A.stabEquiv c γ : MulAction.stabilizer S.G (S.outSec.rep c)) : S.G) = A.gl ((γ : Γ), stabJ γ) := rfl
    rw [e1, hgl, Units.smul_def, stabK_eq_inv, map_inv]

namespace ClassPres

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'} {ρ' : Γ' →* Module.End ℂ W} {J' : Subgroup G'}
  {χ' : J' →* ℂˣ}

theorem mem_stab_transport (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hJ : ∀ x, x ∈ J' ↔ eG.symm x ∈ J) (y : G) (γ : Γ) : eΓ γ ∈ stab ι' J' (eG y) ↔ γ ∈ stab ι J y := by
  rw [mem_stab, mem_stab, hJ, hι]
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]

def stabTransport (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hJ : ∀ x, x ∈ J' ↔ eG.symm x ∈ J) (y : G) : stab ι J y ≃* stab ι' J' (eG y) where
  toFun γ := ⟨eΓ γ, (mem_stab_transport eG eΓ hι hJ y γ).2 γ.2⟩
  invFun γ' := ⟨eΓ.symm γ', (mem_stab_transport eG eΓ hι hJ y _).1 (by rw [MulEquiv.apply_symm_apply]; exact γ'.2)⟩
  left_inv γ := Subtype.ext (eΓ.symm_apply_apply _)
  right_inv γ' := Subtype.ext (eΓ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul eΓ _ _)

theorem stabK_transport (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hJ : ∀ x, x ∈ J' ↔ eG.symm x ∈ J) (y : G) (γ : stab ι J y) :
    ((stabK ι' (stabTransport eG eΓ hι hJ y γ) : J') : G') = eG (stabK ι γ : G) := by
  show ((eG y)⁻¹ * ι' (eΓ (γ : Γ)) * eG y)⁻¹ = eG ((y⁻¹ * ι (γ : Γ) * y)⁻¹)
  rw [hι]
  simp only [map_mul, map_inv]

def transport (P : ClassPres ι S σ ρ J χ) (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ) (hJ : J' = J.map eG.toMonoidHom)
    (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k) : ClassPres ι' S σ ρ' J' χ' :=
  have hJ' : ∀ x, x ∈ J' ↔ eG.symm x ∈ J := fun x => by subst hJ; exact Subgroup.mem_map_equiv
  { y := fun c => eG (P.y c)
    reps := by
      intro h'
      obtain ⟨c, ⟨γ, k, hk⟩, hu⟩ := P.reps (eG.symm h')
      refine ⟨c, ⟨eΓ γ, ⟨eG k, (hJ' _).2 (by rw [MulEquiv.symm_apply_apply]; exact k.2)⟩, ?_⟩, ?_⟩
      · show h' = ι' (eΓ γ) * eG (P.y c) * eG (k : G)
        rw [hι, ← map_mul, ← map_mul, ← hk, MulEquiv.apply_symm_apply]
      · rintro c' ⟨γ', k', hk'⟩
        refine hu c' ⟨eΓ.symm γ', ⟨eG.symm k', (hJ' _).1 k'.2⟩, ?_⟩
        rw [hk']
        have e : ι (eΓ.symm γ') = eG.symm (ι' γ') := by
          rw [MulEquiv.eq_symm_apply, ← hι, MulEquiv.apply_symm_apply]
        rw [e]
        simp only [map_mul, MulEquiv.symm_apply_apply]
    stabI := fun c => (P.stabI c).trans (stabTransport eG eΓ hι hJ' (P.y c))
    coef := P.coef
    coef_li := P.coef_li
    coef_span := P.coef_span
    coef_pair := P.coef_pair
    coef_act := by
      intro c g x
      have hk : stabK ι' (stabTransport eG eΓ hι hJ' (P.y c) (P.stabI c g)) =
          ⟨eG (stabK ι (P.stabI c g) : G), (hJ' _).2 (by rw [MulEquiv.symm_apply_apply]; exact (stabK ι (P.stabI c g)).2)⟩ :=
        Subtype.ext (stabK_transport eG eΓ hι hJ' (P.y c) (P.stabI c g))
      show P.coef (S.ρ c g x) = (χ' (stabK ι' (stabTransport eG eΓ hι hJ' (P.y c) (P.stabI c g))) : ℂ) •
        ρ' (eΓ (P.stabI c g : Γ)) (P.coef x)
      rw [hk, hχ, hρ, P.coef_act] }

end ClassPres

end Formalism.IndefR.Bridge
end
end

section
open NumberField

noncomputable section

namespace Formalism.IndefR.Bridge

open Formalism.L2

section ColPts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Formalism.L2.DIV.Pl E))
  (H : Subgroup (Col.GLG E n SG))

def colJ : Subgroup (Col.UAd hc n) := (Col.JH hc n ST SG H).map (Col.ToUnitaryAdelic hc n ST)

abbrev principalCongruenceSubgroup : Subgroup (Col.UAd hc n) := (Col.K1 hc n ST SG).subgroupOf (Col.UAd hc n)

theorem J0toU_injective : Function.Injective (Col.ToUnitaryAdelic hc n ST) := Subgroup.inclusion_injective _

def colJEquiv : Col.JH hc n ST SG H ≃* colJ hc n ST SG H :=
  (Col.JH hc n ST SG H).equivMapOfInjective _ (J0toU_injective hc n ST)

theorem colJEquiv_symm_coe (k : colJ hc n ST SG H) :
    Col.ToUnitaryAdelic hc n ST (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.J0 hc n ST) = (k : Col.UAd hc n) := by
  rw [← Subgroup.coe_equivMapOfInjective_apply (Col.JH hc n ST SG H) (Col.ToUnitaryAdelic hc n ST) (J0toU_injective hc n ST)]
  exact congrArg Subtype.val ((colJEquiv hc n ST SG H).apply_symm_apply k)

theorem mem_principal_congruence_iff (m : Col.J0 hc n ST) : Col.ToUnitaryAdelic hc n ST m ∈ principalCongruenceSubgroup hc n ST SG ↔ Col.redG hc n ST SG m = 1 := by
  constructor
  · intro h
    obtain ⟨m', hm', he⟩ := Subgroup.mem_subgroupOf.1 h
    have e : m' = m := Subtype.ext he
    rw [← e]
    exact MonoidHom.mem_ker.1 hm'
  · intro h
    exact Col.mem_principal_congruence_of hc n ST SG h

theorem principal_congruence_le_level_subgroup : principalCongruenceSubgroup hc n ST SG ≤ colJ hc n ST SG H := by
  intro a ha
  obtain ⟨m, hm, hma⟩ := Subgroup.mem_subgroupOf.1 ha
  refine Subgroup.mem_map.2 ⟨m, Subgroup.mem_comap.2 ?_, Subtype.ext hma⟩
  rw [MonoidHom.mem_ker.1 hm]
  exact H.one_mem

def colToAdG : Col.URat hc n × colJ hc n ST SG H →* Col.AdG hc n ST SG H :=
  show Col.URat hc n × colJ hc n ST SG H →* Col.URat hc n × (Col.JH hc n ST SG H ⧸ (Col.redH hc n ST SG H).ker) from
    MonoidHom.prodMap (MonoidHom.id _)
      ((QuotientGroup.mk' (Col.redH hc n ST SG H).ker).comp (colJEquiv hc n ST SG H).symm.toMonoidHom)

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Col.GSD K}

variable {hc n ST SG H}

def colGl (o : Col.OnDeco n ST SG H S) : Col.URat hc n × colJ hc n ST SG H →* S.G :=
  o.eG.toMonoidHom.comp ((Col.adHom hc n ST SG H).comp (colToAdG hc n ST SG H))

def colQ (o : Col.OnDeco n ST SG H S) (x : Col.UAd hc n) : S.D :=
  o.eD (Col.decoPt hc n ST SG (QuotientGroup.mk x : Col.adPt hc n ST SG))

variable (o : Col.OnDeco n ST SG H S)

theorem colGl_apply (γ : Col.URat hc n) (k : colJ hc n ST SG H) :
    colGl o (γ, k) = o.eG (Col.ratHom hc n γ, Col.redH hc n ST SG H ((colJEquiv hc n ST SG H).symm k)) := rfl

theorem colGl_surj (hR : Col.RedHSurj hc n ST SG H) : Function.Surjective (colGl (hc := hc) o) := by
  intro g
  obtain ⟨⟨u, h⟩, rfl⟩ := o.eG.surjective g
  obtain ⟨γ, hγ⟩ := (Col.ratHom_bijective hc n).2 u
  obtain ⟨k, hk⟩ := hR h
  refine ⟨(γ, colJEquiv hc n ST SG H k), ?_⟩
  rw [colGl_apply, MulEquiv.symm_apply_apply, hγ, hk]

theorem colGl_ker (γ : Col.URat hc n) (k : colJ hc n ST SG H) :
    colGl o (γ, k) = 1 ↔ γ = 1 ∧ (k : Col.UAd hc n) ∈ principalCongruenceSubgroup hc n ST SG := by
  rw [colGl_apply, MulEquiv.map_eq_one_iff, Prod.mk_eq_one,
    (injective_iff_map_eq_one' _).1 (Col.ratHom_bijective hc n).1, ← colJEquiv_symm_coe, mem_principal_congruence_iff]
  exact and_congr Iff.rfl Subtype.ext_iff

theorem colQ_surj (hS : Col.DecoPtSurj hc n ST SG) : Function.Surjective (colQ (hc := hc) o) := by
  intro d
  obtain ⟨d', rfl⟩ := o.eD.surjective d
  obtain ⟨p, rfl⟩ := hS d'
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
  exact ⟨x, rfl⟩

theorem colQ_fib (x x' : Col.UAd hc n) :
    colQ o x = colQ o x' ↔ ∃ k1 ∈ principalCongruenceSubgroup hc n ST SG, x' = x * k1 := by
  unfold colQ
  rw [o.eD.injective.eq_iff, (Col.decoPt_injective' hc n ST SG).eq_iff, QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, by rw [mul_inv_cancel_left]⟩
  · rintro ⟨k1, hk1, rfl⟩
    rwa [inv_mul_cancel_left]

theorem colQ_eqv (γ : Col.URat hc n) (k : colJ hc n ST SG H) (x : Col.UAd hc n) :
    colQ o (Col.ratIn hc n γ * x * (k : Col.UAd hc n)⁻¹) = colGl o (γ, k) • colQ o x := by
  have e1 : Col.ratIn hc n γ * x * (k : Col.UAd hc n)⁻¹ =
      Col.rawSm hc n ST γ (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.J0 hc n ST) x := by
    unfold Col.rawSm
    rw [colJEquiv_symm_coe]
  have e2 := Col.decorated_point_equivariant hc n ST SG H
    ((γ, (((colJEquiv hc n ST SG H).symm k : Col.JH hc n ST SG H) : Col.JH hc n ST SG H ⧸ (Col.redH hc n ST SG H).ker)) :
      Col.AdG hc n ST SG H) (QuotientGroup.mk x : Col.adPt hc n ST SG)
  unfold colQ
  rw [e1, Col.adSmul_mk] at *
  rw [e2, o.smul]
  rfl

def colAdPts (hS : Col.DecoPtSurj hc n ST SG) : AdPts S (Col.ratIn hc n) (colJ hc n ST SG H) where
  K1 := principalCongruenceSubgroup hc n ST SG
  principal_congruence_le := principal_congruence_le_level_subgroup hc n ST SG H
  q := colQ o
  gl := colGl o
  gl_surj := colGl_surj o (Col.redHSurj_of hc n ST SG H (Col.decorated_lattice_exists hc n ST SG) hS)
  gl_ker := colGl_ker o
  q_surj := colQ_surj o hS
  q_eqv := colQ_eqv o
  q_fib := colQ_fib o

open Classical in

def colAdPtsG (hG : Col.UnimodGenus hc n) (hR : Formalism.L2.DIV.RedSurj) (hT : Formalism.L2.DIV.IsSplitSet (ST ∪ SG))
    (hD : Disjoint ST SG) : AdPts S (Col.ratIn hc n) (colJ hc n ST SG H) :=
  colAdPts o (Col.decoPtSurj_of hc n ST SG hG hR hT hD)

def colClassPres (hS : Col.DecoPtSurj hc n ST SG) (h : S.Ok) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (σ : K →+* ℂ) (ρ : Col.URat hc n →* Module.End ℂ W) (χ : colJ hc n ST SG H →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x'))
    (hK1 : ∀ k : colJ hc n ST SG H, (k : Col.UAd hc n) ∈ principalCongruenceSubgroup hc n ST SG → χ k = 1)
    (hgl : ∀ (γ : Col.URat hc n) (k : colJ hc n ST SG H) (v : S.V),
      coef (S.ρ (colGl o (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v)) :
    ClassPres (Col.ratIn hc n) (S.toCSD h) σ ρ (colJ hc n ST SG H) χ :=
  classPresOf (colAdPts o hS) h σ ρ χ coef hli hspan hpair hK1 hgl

end ColPts

section Forms

variable {X : Col.Fields} (hc : Formalism.BasicNotions.CMData X.F X.E) {n : ℕ} [NeZero n]
  {ST SG : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 X.E))}

end Forms

end Formalism.IndefR.Bridge
end
end
