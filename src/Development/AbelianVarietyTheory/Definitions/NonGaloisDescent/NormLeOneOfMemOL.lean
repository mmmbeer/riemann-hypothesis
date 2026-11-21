import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit

section
noncomputable section

namespace GlobalTheory.Prism

def SemiBC {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module B N] {f : A →+* B} (u : M →ₛₗ[f] N) : Prop :=
  ∀ (Q : Type) [AddCommGroup Q] [Module B Q] (v : M →ₛₗ[f] Q), ∃! w : N →ₗ[B] Q, ∀ x, w (u x) = v x

structure Delta (l : ℕ) (A : Type) [CommRing A] where
  δ : A → A
  δ_one : δ 1 = 0
  δ_mul : ∀ a b, δ (a * b) = a ^ l * δ b + b ^ l * δ a + (l : A) * δ a * δ b
  δ_add : ∀ a b, δ (a + b) = δ a + δ b -
    ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * a ^ k * b ^ (l - k)
  φ : A →+* A
  φ_eq : ∀ a, φ a = a ^ l + (l : A) * δ a

structure Obj (l : ℕ) (R : Type) [CommRing R] where
  A : Type
  [ring : CommRing A]
  D : Delta l A
  I : Ideal A
  inv : Module.Invertible A ↥I
  complete : IsAdicComplete (Ideal.span {(l : A)} ⊔ I) A
  l_mem : (l : A) ∈ I ⊔ I.map D.φ
  bdd : ∃ n : ℕ, ∀ x : A ⧸ I, (∃ m : ℕ, (l : A ⧸ I) ^ m * x = 0) → (l : A ⧸ I) ^ n * x = 0
  str : R →+* A ⧸ I

attribute [instance] Obj.ring

variable {l : ℕ} {R : Type} [CommRing R]

structure Hom (P P' : Obj l R) where
  f : P.A →+* P'.A
  f_δ : ∀ a, f (P.D.δ a) = P'.D.δ (f a)
  f_I : ∀ a ∈ P.I, f a ∈ P'.I
  f_str : ∀ (r : R) (a : P.A), Ideal.Quotient.mk P.I a = P.str r →
    Ideal.Quotient.mk P'.I (f a) = P'.str r

def Hom.id (P : Obj l R) : Hom P P where
  f := RingHom.id _
  f_δ := fun _ => rfl
  f_I := fun _ h => h
  f_str := fun _ _ h => h

def Hom.comp {P P' P'' : Obj l R} (g : Hom P' P'') (f : Hom P P') : Hom P P'' where
  f := g.f.comp f.f
  f_δ := fun a => by simp [f.f_δ, g.f_δ]
  f_I := fun a h => g.f_I _ (f.f_I a h)
  f_str := fun r a h => g.f_str r _ (f.f_str r a h)

def IsFrac {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (d : A)
    (y : LocalizedModule (Submonoid.powers d) M) (m : M) (k : ℕ) : Prop :=
  y = LocalizedModule.mk m (⟨d ^ k, (Submonoid.mem_powers_iff _ _).2 ⟨k, rfl⟩⟩ : ↥(Submonoid.powers d))

structure FCrys (l : ℕ) (R : Type) [CommRing R] where
  M : Obj l R → Type
  [acg : ∀ P, AddCommGroup (M P)]
  [mod : ∀ P, Module P.A (M P)]
  fin : ∀ P, Module.Finite P.A (M P)
  proj : ∀ P, Module.Projective P.A (M P)
  tr : ∀ {P P' : Obj l R} (f : Hom P P'), M P →ₛₗ[f.f] M P'
  tr_bc : ∀ {P P' : Obj l R} (f : Hom P P'), SemiBC (tr f)
  tr_id : ∀ (P : Obj l R) x, tr (Hom.id P) x = x
  tr_comp : ∀ {P P' P'' : Obj l R} (g : Hom P' P'') (f : Hom P P') x,
    tr (g.comp f) x = tr g (tr f x)

  Φ : ∀ (P : Obj l R) (d : ↥P.I), M P →ₛₗ[(algebraMap P.A (Localization.Away (d : P.A))).comp P.D.φ]
    LocalizedModule (Submonoid.powers (d : P.A)) (M P)
  Φ_bc : ∀ (P : Obj l R) (d : ↥P.I), SemiBC (Φ P d)

  Φ_nat : ∀ {P P' : Obj l R} (f : Hom P P') (d : ↥P.I) (d' : ↥P'.I) (x m : M P) (k : ℕ) (n : M P') (j : ℕ),
    IsFrac (d : P.A) (Φ P d x) m k → IsFrac (d' : P'.A) (Φ P' d' (tr f x)) n j →
      ∃ r : ℕ, (f.f d * d') ^ r • ((d' : P'.A) ^ j • tr f m - f.f d ^ k • n) = 0

attribute [instance] FCrys.acg FCrys.mod

structure FHom (E E' : FCrys l R) where
  u : ∀ P : Obj l R, E.M P →ₗ[P.A] E'.M P
  u_tr : ∀ {P P' : Obj l R} (f : Hom P P') x, u P' (E.tr f x) = E'.tr f (u P x)
  u_Φ : ∀ (P : Obj l R) (d : ↥P.I) (x m : E.M P) (k : ℕ),
    IsFrac (d : P.A) (E.Φ P d x) m k → IsFrac (d : P.A) (E'.Φ P d (u P x)) (u P m) k

structure VBun (l : ℕ) (R : Type) [CommRing R] where
  M : Obj l R → Type
  [acg : ∀ P, AddCommGroup (M P)]
  [mod : ∀ P, Module P.A (M P)]
  fin : ∀ P, Module.Finite P.A (M P)
  proj : ∀ P, Module.Projective P.A (M P)
  tr : ∀ {P P' : Obj l R} (f : Hom P P'), M P →ₛₗ[f.f] M P'
  tr_bc : ∀ {P P' : Obj l R} (f : Hom P P'), SemiBC (tr f)
  tr_id : ∀ (P : Obj l R) x, tr (Hom.id P) x = x
  tr_comp : ∀ {P P' P'' : Obj l R} (g : Hom P' P'') (f : Hom P P') x,
    tr (g.comp f) x = tr g (tr f x)

attribute [instance] VBun.acg VBun.mod

def FCrys.toVBun (E : FCrys l R) : VBun l R where
  M := E.M
  fin := E.fin
  proj := E.proj
  tr := E.tr
  tr_bc := E.tr_bc
  tr_id := E.tr_id
  tr_comp := E.tr_comp

def FCrys.Effective (E : FCrys l R) : Prop :=
  ∀ (P : Obj l R) (x : E.M P), ∃ m : E.M P, ∀ d : ↥P.I, IsFrac (d : P.A) (E.Φ P d x) m 0

theorem Delta.δ_zero {A : Type} [CommRing A] (D : Delta l A) : D.δ 0 = 0 := by
  have h := D.δ_add 0 0
  have e : ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * (0 : A) ^ k * (0 : A) ^ (l - k) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [zero_pow (Finset.mem_Ioo.1 hk).1.ne']; simp
  rw [e, add_zero] at h
  linear_combination -h

def Delta.ofLift (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (φ : A →+* A)
    (htf : ∀ x : A, (l : A) * x = 0 → x = 0) (h : ∀ a, ∃ b, φ a = a ^ l + (l : A) * b) : Delta l A where
  δ a := (h a).choose
  δ_one := by
    apply htf
    have := (h 1).choose_spec
    simp only [map_one, one_pow] at this ⊢
    linear_combination -this
  δ_mul a b := by
    rw [← sub_eq_zero]; apply htf
    have h1 := (h a).choose_spec
    have h2 := (h b).choose_spec
    have h3 := (h (a * b)).choose_spec
    have h4 := map_mul φ a b
    generalize (h a).choose = x at *
    generalize (h b).choose = y at *
    generalize (h (a*b)).choose = z at *
    rw [h1, h2, h3, mul_pow] at h4
    linear_combination h4
  δ_add a b := by
    rw [← sub_eq_zero]; apply htf
    have h1 := (h a).choose_spec
    have h2 := (h b).choose_spec
    have h3 := (h (a + b)).choose_spec
    have h4 := map_add φ a b
    generalize (h a).choose = x at *
    generalize (h b).choose = y at *
    generalize (h (a+b)).choose = z at *
    have h5 : (a + b) ^ l = a ^ l + b ^ l + (l : A) *
        ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * a ^ k * b ^ (l - k) := by
      rw [add_pow_prime_eq' hl.out]
      congr 2
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [h1, h2, h3, h5] at h4
    linear_combination h4
  φ := φ
  φ_eq a := (h a).choose_spec

@[simp] theorem Delta.ofLift_φ (l : ℕ) [Fact l.Prime] {A : Type} [CommRing A] (φ : A →+* A)
    (htf : ∀ x : A, (l : A) * x = 0 → x = 0) (h : ∀ a, ∃ b, φ a = a ^ l + (l : A) * b) :
    (Delta.ofLift l φ htf h).φ = φ := rfl

theorem Delta.map_φ_of_map_δ {A B : Type} [CommRing A] [CommRing B] (D : Delta l A) (D' : Delta l B)
    (f : A →+* B) (h : ∀ a, f (D.δ a) = D'.δ (f a)) (a : A) : f (D.φ a) = D'.φ (f a) := by
  simp [D.φ_eq, D'.φ_eq, h]

theorem Delta.map_δ_of_map_φ {A B : Type} [CommRing A] [CommRing B] (D : Delta l A) (D' : Delta l B)
    (htf : ∀ x : B, (l : B) * x = 0 → x = 0) (f : A →+* B) (h : ∀ a, f (D.φ a) = D'.φ (f a)) (a : A) :
    f (D.δ a) = D'.δ (f a) := by
  rw [← sub_eq_zero]; apply htf
  have := h a
  simp only [D.φ_eq, D'.φ_eq, map_add, map_mul, map_pow, map_natCast] at this
  linear_combination this

theorem Hom.f_φ {P P' : Obj l R} (f : Hom P P') (a : P.A) : f.f (P.D.φ a) = P'.D.φ (f.f a) :=
  P.D.map_φ_of_map_δ P'.D f.f f.f_δ a

theorem Hom.ext' {P P' : Obj l R} {f g : Hom P P'} (h : f.f = g.f) : f = g := by
  cases f; cases g; cases h; rfl

theorem Delta.l_mem_of_isUnit (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {q : A}
    (hq : IsUnit (D.δ q)) : (l : A) ∈ Ideal.span {q} ⊔ (Ideal.span {q}).map D.φ := by
  obtain ⟨v, hv⟩ := hq.exists_right_inv
  have e : (l : A) = v * (D.φ q - q ^ l) := by
    rw [D.φ_eq]; linear_combination (-(l : A)) * hv
  rw [e]
  refine Ideal.mul_mem_left _ _ (Ideal.sub_mem _ ?_ ?_)
  · exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self q))
  · exact Ideal.mem_sup_left (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self q) _ hl)

theorem invertible_span_singleton {A : Type} [CommRing A] {q : A} (hq : q ∈ nonZeroDivisors A) :
    Module.Invertible A ↥(Ideal.span {q}) :=
  Module.Invertible.congr (M := A)
    ((LinearEquiv.ofInjective (LinearMap.toSpanSingleton A A q) (by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      exact fun a h => (mem_nonZeroDivisors_iff.1 hq).2 a h)).trans
      (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range A A q).symm))

def Obj.ofDistinguished (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) (q : A)
    (hq : q ∈ nonZeroDivisors A) (hδ : IsUnit (D.δ q))
    (hc : IsAdicComplete (Ideal.span {(l : A)} ⊔ Ideal.span {q}) A)
    (hb : ∃ n : ℕ, ∀ x : A ⧸ Ideal.span {q}, (∃ m : ℕ, (l : A ⧸ Ideal.span {q}) ^ m * x = 0) →
      (l : A ⧸ Ideal.span {q}) ^ n * x = 0)
    (str : R →+* A ⧸ Ideal.span {q}) : Obj l R where
  A := A
  D := D
  I := Ideal.span {q}
  inv := invertible_span_singleton hq
  complete := hc
  l_mem := D.l_mem_of_isUnit hl hδ
  bdd := hb
  str := str

def Obj.restrict {R' : Type} [CommRing R'] (g : R →+* R') (P : Obj l R') : Obj l R where
  A := P.A
  D := P.D
  I := P.I
  inv := P.inv
  complete := P.complete
  l_mem := P.l_mem
  bdd := P.bdd
  str := P.str.comp g

def Hom.restrict {R' : Type} [CommRing R'] (g : R →+* R') {P P' : Obj l R'} (f : Hom P P') :
    Hom (P.restrict g) (P'.restrict g) where
  f := f.f
  f_δ := f.f_δ
  f_I := f.f_I
  f_str r a h := f.f_str (g r) a h

def FCrys.pullback {R' : Type} [CommRing R'] (g : R →+* R') (E : FCrys l R) : FCrys l R' where
  M P := E.M (P.restrict g)
  acg P := E.acg (P.restrict g)
  mod P := E.mod (P.restrict g)
  fin P := E.fin (P.restrict g)
  proj P := E.proj (P.restrict g)
  tr f := E.tr (f.restrict g)
  tr_bc f := E.tr_bc (f.restrict g)
  tr_id P := E.tr_id (P.restrict g)
  tr_comp f' f := E.tr_comp (f'.restrict g) (f.restrict g)
  Φ P := E.Φ (P.restrict g)
  Φ_bc P := E.Φ_bc (P.restrict g)
  Φ_nat f := E.Φ_nat (f.restrict g)

def Obj.crys (l : ℕ) [hl : Fact l.Prime] : Obj l ℤ_[l] where
  A := ℤ_[l]
  D := Delta.ofLift l (RingHom.id _)
    (fun x hx => (mul_eq_zero.1 hx).resolve_left (by exact_mod_cast hl.out.ne_zero))
    (fun a => by
      have : a - a ^ l ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
        simp [RingHom.mem_ker]
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
      obtain ⟨b, hb⟩ := this
      exact ⟨b, by simp only [RingHom.id_apply]; linear_combination hb⟩)
  I := Ideal.span {(l : ℤ_[l])}
  inv := invertible_span_singleton (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hl.out.ne_zero))
  complete := by
    rw [sup_idem, ← PadicInt.maximalIdeal_eq_span_p]; infer_instance
  l_mem := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  bdd := ⟨1, fun x _ => by
    have : ((l : ℕ) : ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l])}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    simp [this]⟩
  str := Ideal.Quotient.mk _


theorem semiBC_self {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : SemiBC f.toSemilinearMap := by
  intro Q _ _ v
  refine ⟨LinearMap.toSpanSingleton B Q (v 1), fun x => ?_, fun w hw => ?_⟩
  · have := v.map_smulₛₗ x 1
    simp at this
    simp [this]
  · ext
    have := hw 1
    simpa using this

def FCrys.unit (l : ℕ) (R : Type) [CommRing R] : FCrys l R where
  M P := P.A
  fin _ := inferInstance
  proj _ := inferInstance
  tr f := f.f.toSemilinearMap
  tr_bc f := semiBC_self f.f
  tr_id _ _ := rfl
  tr_comp _ _ _ := rfl
  Φ P d := ((algebraMap P.A (Localization.Away (d : P.A))).comp P.D.φ).toSemilinearMap
  Φ_bc P d := semiBC_self _
  Φ_nat := by
    intro P P' f d d' x m k n j h1 h2
    have key : ∀ {A : Type} [CommRing A] (e y m : A) (k : ℕ),
        IsFrac e (algebraMap A (Localization.Away e) y) m k → ∃ a : ℕ, e ^ a * (e ^ k * y) = e ^ a * m := by
      intro A _ e y m k h
      have h' : LocalizedModule.mk y (1 : Submonoid.powers e) = _ := h
      rw [LocalizedModule.mk_eq] at h'
      obtain ⟨⟨_, a, rfl⟩, ha⟩ := h'
      exact ⟨a, by simpa [Submonoid.smul_def] using ha⟩
    obtain ⟨a, ha⟩ := key _ _ _ _ h1
    obtain ⟨b, hb⟩ := key _ _ _ _ h2
    have ha' := congrArg f.f ha
    simp only [map_mul, map_pow, f.f_φ] at ha'
    refine ⟨a + b, ?_⟩
    change (f.f d * d') ^ (a + b) * ((d' : P'.A) ^ j * f.f m - f.f d ^ k * n) = 0
    change (d' : P'.A) ^ b * ((d' : P'.A) ^ j * P'.D.φ (f.f x)) = _ at hb
    linear_combination (-(f.f d) ^ b * (d' : P'.A) ^ (a + b + j)) * ha' +
      (f.f d ^ (a + b + k) * (d' : P'.A) ^ a) * hb


def VBun.unit (l : ℕ) (R : Type) [CommRing R] : VBun l R := (FCrys.unit l R).toVBun

def FHom.id (E : FCrys l R) : FHom E E where
  u _ := LinearMap.id
  u_tr _ _ := rfl
  u_Φ _ _ _ _ _ h := h

def FHom.comp {E E' E'' : FCrys l R} (v : FHom E' E'') (u : FHom E E') : FHom E E'' where
  u P := (v.u P).comp (u.u P)
  u_tr f x := by simp [u.u_tr, v.u_tr]
  u_Φ P d x m k h := v.u_Φ P d _ _ k (u.u_Φ P d x m k h)

instance FCrys.unit_crys_nontrivial (l : ℕ) [Fact l.Prime] :
    Nontrivial ((FCrys.unit l ℤ_[l]).M (Obj.crys l)) :=
  inferInstanceAs (Nontrivial ℤ_[l])

instance VBun.unit_crys_nontrivial (l : ℕ) [Fact l.Prime] :
    Nontrivial ((VBun.unit l ℤ_[l]).M (Obj.crys l)) :=
  inferInstanceAs (Nontrivial ℤ_[l])

theorem FCrys.unit_crys_Φ_ne_zero (l : ℕ) [hl : Fact l.Prime] :
    (FCrys.unit l ℤ_[l]).Φ (Obj.crys l) ⟨(l : ℤ_[l]), Ideal.mem_span_singleton_self _⟩ (1 : ℤ_[l]) ≠ 0 := by
  intro h
  have h' : LocalizedModule.mk (1 : ℤ_[l]) (1 : Submonoid.powers (l : ℤ_[l])) =
      LocalizedModule.mk (0 : ℤ_[l]) 1 := by
    rw [LocalizedModule.zero_mk]; exact h
  rw [LocalizedModule.mk_eq] at h'
  obtain ⟨⟨_, r, rfl⟩, h'⟩ := h'
  simp [Submonoid.smul_def, hl.out.ne_zero] at h'

example (l : ℕ) [hl : Fact l.Prime] :
    (Obj.crys l).D.δ (l : ℤ_[l]) = (1 : ℤ_[l]) - (l : ℤ_[l]) ^ (l - 1) := by
  have h : (l : ℤ_[l]) = (l : ℤ_[l]) ^ l + (l : ℤ_[l]) * (show ℤ_[l] from (Obj.crys l).D.δ (l : ℤ_[l])) :=
    (Obj.crys l).D.φ_eq (l : ℤ_[l])
  have h0 : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have h1 : (l : ℤ_[l]) ^ l = (l : ℤ_[l]) * (l : ℤ_[l]) ^ (l - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hl.out.one_le]
  refine mul_left_cancel₀ h0 (b := (show ℤ_[l] from (Obj.crys l).D.δ (l : ℤ_[l]))) ?_
  linear_combination -h - h1

example {A : Type} [CommRing A] (D : Delta 2 A) : D.δ 2 = -1 := by
  have hI : Finset.Ioo 0 2 = {1} := by decide
  have h1 := D.δ_add 1 1
  rw [hI, D.δ_one, one_add_one_eq_two] at h1
  simpa using h1

end GlobalTheory.Prism
end
end

section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.Prism

variable {l : ℕ} [hl : Fact l.Prime]

variable (l) in

def galTilt : GQ l →* (OCb l ≃+* OCb l) where
  toFun g := RingEquiv.ofRingHom (Per.σF g) (Per.σF g⁻¹)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← GlobalTheory.RingBasics.σF_mul, mul_inv_cancel, GlobalTheory.RingBasics.σF_one]; rfl)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← GlobalTheory.RingBasics.σF_mul, inv_mul_cancel, GlobalTheory.RingBasics.σF_one]; rfl)
  map_one' := RingEquiv.ext fun x => GlobalTheory.RingBasics.σF_one x
  map_mul' g h := RingEquiv.ext fun x => GlobalTheory.RingBasics.σF_mul g h x

theorem galTilt_apply (g : GQ l) (x : OCb l) : galTilt l g x = Per.σF g x := rfl

variable (l) in

def galW : GQ l →* (WCb l ≃ₐ[ℤ_[l]] WCb l) where
  toFun g := mapAlgEquivW l (autCb l (galTilt l g))
  map_one' := by
    ext x n
    simp [mapAlgEquivW, mapEquivW, WittVector.map_coeff, autCb_one]
  map_mul' g h := by
    ext x n
    simp [mapAlgEquivW, mapEquivW, WittVector.map_coeff, autCb_mul]

theorem galW_inclW (g : GQ l) (a : Ainf l) : galW l g (inclW l a) = inclW l (Per.σA g a) :=
  WittVector.ext fun n => (autCb_alg l (galTilt l g) (a.coeff n)).trans
    (congrArg (algebraMap (OCb l) (Cb l)) (GlobalTheory.RingIface.sigA_coeff l g a n).symm)

theorem frobW_inclW (a : Ainf l) : frobW l (inclW l a) = inclW l (WittVector.frobenius a) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  exact WittVector.ext fun n => (map_pow (algebraMap (OCb l) (Cb l)) (a.coeff n) l).symm

theorem locAinf_actT_eq {P : LocPrime l} (AI : LocAinf l P) : AI.actT = galTilt l :=
  MonoidHom.ext fun g => RingEquiv.ext fun x => GlobalTheory.MemLoc.locAinf_actT AI g x

theorem locAinf_actWCbHom_eq {P : LocPrime l} (AI : LocAinf l P) : AI.actWCbHom = galW l :=
  MonoidHom.ext fun g => by
    change mapAlgEquivW l (autCb l (AI.actT g)) = mapAlgEquivW l (autCb l (galTilt l g))
    rw [locAinf_actT_eq]

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem ainf_torsionFree (x : Ainf l) (h : (l : Ainf l) * x = 0) : x = 0 :=
  WittVector.eq_zero_of_p_mul_eq_zero x (by rw [mul_comm, h])

theorem frobenius_eq_pow_add (a : Ainf l) : ∃ b, WittVector.frobenius a = a ^ l + (l : Ainf l) * b := by
  have h : WittVector.frobenius a - a ^ l ∈ RingHom.ker (WittVector.constantCoeff (p := l) (R := OCb l)) := by
    rw [RingHom.mem_ker, map_sub, map_pow, WittVector.constantCoeff_apply,
      WittVector.coeff_frobenius_charP, WittVector.constantCoeff_apply, sub_self]
  rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by linear_combination hb⟩

variable (l) in

def ainfDelta : Delta l (Ainf l) :=
  Delta.ofLift l WittVector.frobenius ainf_torsionFree frobenius_eq_pow_add

variable (l) in

theorem theta_onto : Function.Surjective (Per.θ l) := by
  refine surjective_fontaineTheta fun x => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ_[l]) hl.out.pos
  have hy1 : y ∈ 𝓞_ℂ_[l] := by
    have := (GlobalTheory.RingBasics.mem_OC _).1 x.2
    rw [← hy, norm_pow] at this
    exact (GlobalTheory.RingBasics.mem_OC _).2 ((pow_le_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 this)
  refine ⟨Ideal.Quotient.mk _ ⟨y, hy1⟩, ?_⟩
  rw [frobenius_def, ← map_pow]
  exact congrArg _ (Subtype.ext hy)

variable (l) in

theorem exists_generator : ∃ ξ : Ainf l, RingHom.ker (Per.θ l) = Ideal.span {ξ} ∧ ξ ≠ 0 ∧
    Per.θ l (WittVector.frobenius ξ) = (l : OC l) := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have h : Per.θ l (WittVector.frobenius (GlobalTheory.MemLoc.xi e)) = (l : OC l) := by
    have h2 : Per.θ l (WittVector.frobenius (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e))) = 1 := by
      rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
        frobeniusEquiv_symm_pow_p, WittVector.fontaineTheta_teichmuller, he]
    simp only [GlobalTheory.MemLoc.xi, map_sum, map_pow, h2]
    simp
  refine ⟨GlobalTheory.MemLoc.xi e, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE, fun h0 => ?_, h⟩
  rw [h0, map_zero, map_zero] at h
  exact (Nat.cast_ne_zero.2 hl.out.ne_zero) h.symm

theorem isUnit_inclW_of_span {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) :
    IsUnit (inclW l d) := by
  refine WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => ?_
  have h0 : d ∈ RingHom.ker (WittVector.constantCoeff (p := l) (R := OCb l)) :=
    IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm)
  rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h0
  obtain ⟨a, ha⟩ := h0
  have h1 : Per.θ l d = 0 := by
    rw [← RingHom.mem_ker, ← hd]; exact Ideal.mem_span_singleton_self d
  have h2 : a ∈ Ideal.span {d} := by
    rw [ha, map_mul, map_natCast] at h1
    rw [hd]
    exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hl.out.ne_zero)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h2
  have h3 : (1 - (l : Ainf l) * b) * d = 0 := by linear_combination ha - (l : Ainf l) * hb
  rcases mul_eq_zero.1 h3 with h4 | h4
  · have := congrArg (WittVector.constantCoeff (p := l) (R := OCb l)) h4
    rw [map_sub, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, sub_zero, map_one, map_zero] at this
    exact one_ne_zero this
  · obtain ⟨ξ, h5, h6, -⟩ := exists_generator l
    apply h6
    have h7 := Ideal.mem_span_singleton_self ξ
    rwa [← h5, ← hd, h4, Ideal.span_singleton_zero, Ideal.mem_bot] at h7

variable (l) in

def ainfQuot : (Ainf l ⧸ RingHom.ker (Per.θ l)) ≃+* OC l :=
  RingHom.quotientKerEquivOfSurjective (theta_onto l)


variable (l) in

def ainfC : Obj l (OC l) where
  A := Ainf l
  D := ainfDelta l
  I := RingHom.ker (Per.θ l)
  inv := by
    obtain ⟨ξ, h, h0, -⟩ := exists_generator l
    rw [h]
    exact invertible_span_singleton (mem_nonZeroDivisors_of_ne_zero h0)
  complete := by
    obtain ⟨ξ, h, -, -⟩ := exists_generator l
    have h1 : Per.θ l ξ = 0 := by
      rw [← RingHom.mem_ker, h]; exact Ideal.mem_span_singleton_self ξ
    rw [h, ← Ideal.span_insert]
    exact (GlobalTheory.Per.AinfComplete.main l ξ fun hu => (hu.map (Per.θ l)).ne_zero h1).1
  l_mem := by
    obtain ⟨ξ, h, -, h1⟩ := exists_generator l
    have e : (l : Ainf l) = ((l : Ainf l) - WittVector.frobenius ξ) + WittVector.frobenius ξ := by ring
    rw [e]
    refine Submodule.add_mem_sup ?_ (Ideal.mem_map_of_mem (ainfDelta l).φ ?_)
    · rw [RingHom.mem_ker, map_sub, h1, map_natCast, sub_self]
    · rw [h]; exact Ideal.mem_span_singleton_self ξ
  bdd := ⟨0, fun x ⟨m, hm⟩ => by
    have h := congrArg (ainfQuot l) hm
    rw [map_mul, map_pow, map_natCast, map_zero] at h
    have h2 := (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
    rw [pow_zero, one_mul]
    exact (ainfQuot l).injective (h2.trans (map_zero _).symm)⟩
  str := (ainfQuot l).symm.toRingHom

theorem norm_le_one_of_mem_OL (K : FinExt l) (x : ↥(OL K)) : ‖((x : ↥K.1) : Om l)‖ ≤ 1 := by
  have h : IsIntegral ℤ_[l] ((x : ↥K.1) : Om l) :=
    (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).2 x.2
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral _))]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact ((minpoly ℤ_[l] _).coeff n).2

def intToOC (K : FinExt l) : ↥(OL K) →+* OC l :=
  ((algebraMap (Om l) ℂ_[l]).comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)).codRestrict _ fun x =>
    (GlobalTheory.RingBasics.mem_OC _).2 ((PadicComplex.norm_extends l _).trans_le (norm_le_one_of_mem_OL K x))

theorem coe_intToOC (K : FinExt l) (x : ↥(OL K)) :
    ((intToOC K x : OC l) : ℂ_[l]) = (((x : ↥K.1) : Om l) : ℂ_[l]) := rfl

def ainfObj (K : FinExt l) : Obj l ↥(OL K) := (ainfC l).restrict (intToOC K)

theorem ainfObj_φ_bijective (K : FinExt l) : Function.Bijective (ainfObj K).D.φ :=
  (WittVector.frobeniusEquiv l (OCb l)).bijective

structure IsAinf (K : FinExt l) (P : Obj l ↥(OL K)) (e : P.A ≃+* Ainf l) : Prop where
  e_φ : ∀ a, e (P.D.φ a) = WittVector.frobenius (e a)
  e_I : ∀ a, a ∈ P.I ↔ Per.θ l (e a) = 0
  e_str : ∀ (x : ↥(OL K)) (a : P.A), Ideal.Quotient.mk P.I a = P.str x →
    ((Per.θ l (e a) : OC l) : ℂ_[l]) = (((x : ↥K.1) : Om l) : ℂ_[l])

def ainfId (K : FinExt l) : (ainfObj K).A ≃+* Ainf l := RingEquiv.refl (Ainf l)

theorem isAinf_ainfObj (K : FinExt l) : IsAinf K (ainfObj K) (ainfId K) where
  e_φ _ := rfl
  e_I _ := Iff.rfl
  e_str x a h := by
    have h1 : ainfQuot l (Ideal.Quotient.mk _ a) = ainfQuot l ((ainfQuot l).symm (intToOC K x)) :=
      congrArg (ainfQuot l) h
    rw [RingEquiv.apply_symm_apply] at h1
    exact congrArg Subtype.val h1

namespace IsAinf

variable {K : FinExt l} {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l}

theorem mk_eq_str_iff (H : IsAinf K P e) (x : ↥(OL K)) (a : P.A) :
    Ideal.Quotient.mk P.I a = P.str x ↔ Per.θ l (e a) = intToOC K x := by
  refine ⟨fun h => Subtype.ext (H.e_str x a h), fun h => ?_⟩
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (P.str x)
  rw [← hb, Ideal.Quotient.eq, H.e_I, map_sub, map_sub, h, sub_eq_zero]
  exact (Subtype.ext (H.e_str x b hb)).symm

theorem map_I (H : IsAinf K P e) : P.I.map e = RingHom.ker (Per.θ l) := by
  ext a
  obtain ⟨a, rfl⟩ := e.surjective a
  rw [Ideal.apply_mem_of_equiv_iff, H.e_I, RingHom.mem_ker]

theorem exists_generator (H : IsAinf K P e) : ∃ d : ↥P.I, Ideal.span {(d : P.A)} = P.I ∧ (d : P.A) ≠ 0 := by
  obtain ⟨ξ, h, h0, -⟩ := Prism.exists_generator l
  obtain ⟨d, rfl⟩ := e.surjective ξ
  have key : ∀ a, a ∈ Ideal.span {d} ↔ a ∈ P.I := fun a => by
    rw [H.e_I, ← RingHom.mem_ker, h, Ideal.mem_span_singleton, Ideal.mem_span_singleton, map_dvd_iff]
  exact ⟨⟨d, (key d).1 (Ideal.mem_span_singleton_self d)⟩, Ideal.ext key,
    fun h1 => h0 (by rw [show d = 0 from h1, map_zero])⟩

theorem isUnit_inclW (H : IsAinf K P e) {d : P.A} (hd : Ideal.span {d} = P.I) : IsUnit (inclW l (e d)) :=
  isUnit_inclW_of_span (by rw [← H.map_I, ← hd, Ideal.map_span, Set.image_singleton])

def galHom (H : IsAinf K P e) (g : ↥(GK K)) : Hom P P where
  f := e.symm.toRingHom.comp ((Per.σA (g : GQ l)).comp e.toRingHom)
  f_δ := P.D.map_δ_of_map_φ P.D
    (fun x hx => e.injective (by
      rw [map_zero]; apply ainf_torsionFree; rw [← map_natCast e, ← map_mul, hx, map_zero]))
    _ fun a => e.injective (by
      change e (e.symm (Per.σA (g : GQ l) (e (P.D.φ a)))) = e (P.D.φ (e.symm (Per.σA (g : GQ l) (e a))))
      rw [H.e_φ, H.e_φ, e.apply_symm_apply, e.apply_symm_apply, WittVector.frobenius_eq_map_frobenius]
      exact WittVector.ext fun n => ((GlobalTheory.RingIface.sigA_coeff l (g : GQ l) _ n).trans
        (map_pow (Per.σF (g : GQ l)) ((e a).coeff n) l)).trans
        (congrArg (· ^ l) (GlobalTheory.RingIface.sigA_coeff l (g : GQ l) (e a) n).symm))
  f_I a ha := by
    rw [H.e_I] at ha ⊢
    change Per.θ l (e (e.symm (Per.σA (g : GQ l) (e a)))) = 0
    rw [e.apply_symm_apply, GlobalTheory.RingBasics.θ_σA, ha, map_zero]
  f_str x a h := by
    rw [H.mk_eq_str_iff] at h ⊢
    change Per.θ l (e (e.symm (Per.σA (g : GQ l) (e a)))) = _
    rw [e.apply_symm_apply, GlobalTheory.RingBasics.θ_σA, h]
    apply Subtype.ext
    refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) _).trans ?_
    change Per.σC (g : GQ l) (((x : ↥K.1) : Om l) : ℂ_[l]) = (((x : ↥K.1) : Om l) : ℂ_[l])
    rw [GlobalTheory.RingBasics.σC_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (x : ↥K.1).2]

theorem e_galHom (H : IsAinf K P e) (g : ↥(GK K)) (a : P.A) :
    e ((H.galHom g).f a) = Per.σA (g : GQ l) (e a) := e.apply_symm_apply _

theorem eq_galHom (H : IsAinf K P e) (g : ↥(GK K)) (h : Hom P P)
    (hh : ∀ a, e (h.f a) = Per.σA (g : GQ l) (e a)) : h = H.galHom g :=
  Hom.ext' (RingHom.ext fun a => e.injective ((hh a).trans (H.e_galHom g a).symm))

theorem galHom_one (H : IsAinf K P e) : H.galHom 1 = Hom.id P :=
  (H.eq_galHom 1 _ fun a => (GlobalTheory.RingBasics.σA_one (e a)).symm).symm

theorem galHom_mul (H : IsAinf K P e) (g h : ↥(GK K)) :
    H.galHom (g * h) = (H.galHom g).comp (H.galHom h) :=
  (H.eq_galHom (g * h) _ fun a => by
    change e ((H.galHom g).f ((H.galHom h).f a)) = _
    rw [e_galHom, e_galHom, ← GlobalTheory.RingBasics.σA_mul]; rfl).symm

end IsAinf

def ainfHom (K : FinExt l) (g : ↥(GK K)) : Hom (ainfObj K) (ainfObj K) := (isAinf_ainfObj K).galHom g



structure Realises (K : FinExt l) (E : FCrys l ↥(OL K)) (P : Obj l ↥(OL K))
    (e : P.A ≃+* Ainf l) (T : Type) [AddCommGroup T] [Module ℤ_[l] T]
    (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T))
    (j : E.M P →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T)) : Prop where
  ainf : IsAinf K P e
  bc : SemiBC j
  j_φ : ∀ (d : ↥P.I), (d : P.A) ≠ 0 → ∀ (x m : E.M P) (k : ℕ), IsFrac (d : P.A) (E.Φ P d x) m k →
    inclW l (e d) ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (j x) = j m
  j_act : ∀ (g : ↥(GK K)) (x : E.M P),
    j (E.tr (ainf.galHom g) x) = TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (j x)

def IsRealisation (K : FinExt l) (E : FCrys l ↥(OL K)) (T : Type) [AddCommGroup T] [Module ℤ_[l] T]
    (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) : Prop :=
  ∃ j, Realises K E (ainfObj K) (ainfId K) T ρ j

theorem SemiBC.hom_ext {A B M N Q : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [AddCommGroup Q] [Module B Q] {f : A →+* B} {u : M →ₛₗ[f] N}
    (h : SemiBC u) {w w' : N →ₗ[B] Q} (hw : ∀ x, w (u x) = w' (u x)) : w = w' :=
  (h Q (w'.comp u)).unique hw fun _ => rfl

theorem SemiBC.comp_equiv {A B M N N' : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [AddCommGroup N'] [Module B N'] {f : A →+* B} {u : M →ₛₗ[f] N}
    (h : SemiBC u) (s : N ≃ₗ[B] N') : SemiBC (s.toLinearMap.comp u) := by
  intro Q _ _ v
  obtain ⟨w, hw, hu⟩ := h Q v
  refine ⟨w.comp s.symm.toLinearMap, fun x => by simp [hw], fun w' hw' => ?_⟩
  rw [← hu (w'.comp s.toLinearMap) hw']
  ext y; simp

theorem exists_isFrac {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (d : A)
    (y : LocalizedModule (Submonoid.powers d) M) : ∃ m k, IsFrac d y m k := by
  induction y using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨_, k, rfl⟩ := s
    exact ⟨m, k, rfl⟩

theorem FCrys.frac_agree {l : ℕ} {R : Type} [CommRing R] (E : FCrys l R) (P : Obj l R) [IsDomain P.A] (d d₀ : ↥P.I)
    (hd : (d : P.A) ≠ 0) (h0 : (d₀ : P.A) ≠ 0) (x m n : E.M P) (k i : ℕ)
    (h : IsFrac (d : P.A) (E.Φ P d x) m k) (hn : IsFrac (d₀ : P.A) (E.Φ P d₀ x) n i) :
    (d₀ : P.A) ^ i • m = (d : P.A) ^ k • n := by
  have := E.proj P
  obtain ⟨r, hr⟩ := E.Φ_nat (Hom.id P) d d₀ x m k n i h (by rw [E.tr_id]; exact hn)
  rw [E.tr_id] at hr
  exact sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ (mul_ne_zero hd h0)))

theorem smul_eq_of_isUnit {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} (u : M →ₛₗ[f] N) {d d₀ : A} (hu : IsUnit (f d₀)) {m n : M}
    {k i : ℕ} (h : d₀ ^ i • m = d ^ k • n) {y : N} (hy : f d₀ ^ i • y = u n) : f d ^ k • y = u m := by
  have h2 := congrArg u h
  rw [u.map_smulₛₗ, u.map_smulₛₗ, map_pow, map_pow, ← hy, smul_comm] at h2
  exact ((hu.pow i).smul_left_cancel.1 h2).symm

theorem eq_of_isFrac {A : Type} [CommRing A] [IsDomain A] {d : A} (hd : d ≠ 0) (y m : A) (k : ℕ)
    (h : IsFrac d (algebraMap A (Localization.Away d) y) m k) : m = d ^ k * y := by
  have h' : LocalizedModule.mk y (1 : Submonoid.powers d) = _ := h
  rw [LocalizedModule.mk_eq] at h'
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := h'
  have h1 : d ^ a * (d ^ k * y) = d ^ a * m := by simpa [Submonoid.smul_def] using ha
  exact (mul_left_cancel₀ (pow_ne_zero _ hd) h1).symm

instance faithfullyFlat_WCb : Module.FaithfullyFlat ℤ_[l] (WCb l) := by
  have hi : Function.Injective (algebraMap ℤ_[l] (WCb l)) :=
    (WittVector.map_injective _ (ZMod.castHom_injective (Cb l))).comp (WittVector.equiv l).symm.injective
  have : Module.IsTorsionFree ℤ_[l] (WCb l) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hi
  rw [Module.FaithfullyFlat.iff_flat_and_proper_ideal]
  refine ⟨inferInstance, fun I hI h => ?_⟩
  have h1 : I • (⊤ : Submodule ℤ_[l] (WCb l)) ≤
      (RingHom.ker (WittVector.constantCoeff (p := l) (R := Cb l))).restrictScalars ℤ_[l] := by
    refine Submodule.smul_le.2 fun r hr y _ => ?_
    have h2 := IsLocalRing.le_maximalIdeal hI hr
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h2
    obtain ⟨c, rfl⟩ := h2
    rw [Submodule.restrictScalars_mem, RingHom.mem_ker, Algebra.smul_def, map_mul, map_mul, map_natCast,
      map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, zero_mul]
  have h3 := h1 (h.ge (Submodule.mem_top (x := (1 : WCb l))))
  rw [Submodule.restrictScalars_mem, RingHom.mem_ker, map_one] at h3
  exact one_ne_zero h3

theorem one_tmul_injective (T : Type) [AddCommGroup T] [Module ℤ_[l] T] :
    Function.Injective fun t : T => (1 : WCb l) ⊗ₜ[ℤ_[l]] t :=
  Module.FaithfullyFlat.tensorProduct_mk_injective (A := ℤ_[l]) (B := WCb l) T

theorem SemiBC.finite_projective {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) [Module.Finite A M]
    [Module.Projective A M] : Module.Finite B N ∧ Module.Projective B N := by
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let v : M →ₛₗ[f] (Fin n → B) :=
    { toFun := fun x i => f (s x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  let Q : (Fin n → B) →ₗ[B] N := Fintype.linearCombination B fun i => u (p (Pi.single i 1))
  have hQ : Q.comp S = LinearMap.id := h.hom_ext fun x => by
    rw [LinearMap.comp_apply, hS, LinearMap.id_apply, Fintype.linearCombination_apply]
    have h1 : x = ∑ i, s x i • p (Pi.single i 1) := by
      conv_lhs => rw [← LinearMap.id_apply (R := A) x, ← hps, LinearMap.comp_apply, pi_eq_sum_univ' (s x)]
      simp
    conv_rhs => rw [h1, map_sum]
    exact Finset.sum_congr rfl fun i _ => (u.map_smulₛₗ _ _).symm
  exact ⟨Module.Finite.of_surjective Q fun y => ⟨S y, LinearMap.congr_fun hQ y⟩,
    Module.Projective.of_split S Q hQ⟩

namespace Realises

variable {K : FinExt l} {E : FCrys l ↥(OL K)} {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l}
  {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {ρ ρ' : ↥(GK K) → (T →ₗ[ℤ_[l]] T)}
  {j : E.M P →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] T)}

theorem of_generator (H : IsAinf K P e) (bc : SemiBC j) (d₀ : ↥P.I) (hd : Ideal.span {(d₀ : P.A)} = P.I)
    (hφ : ∀ (x m : E.M P) (k : ℕ), IsFrac (d₀ : P.A) (E.Φ P d₀ x) m k →
      inclW l (e d₀) ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (j x) = j m)
    (hact : ∀ (g : ↥(GK K)) (x : E.M P),
      j (E.tr (H.galHom g) x) = TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (j x)) :
    Realises K E P e T ρ j := by
  refine ⟨H, bc, fun d hd0 x m k h => ?_, hact⟩
  have : IsDomain P.A := e.toMulEquiv.isDomain
  have hu := H.isUnit_inclW hd
  have h0 : (d₀ : P.A) ≠ 0 := fun h0 => hu.ne_zero (by rw [h0, map_zero, map_zero])
  obtain ⟨n, i, hn⟩ := exists_isFrac (d₀ : P.A) (E.Φ P d₀ x)
  exact smul_eq_of_isUnit j hu (E.frac_agree P d d₀ hd0 h0 x m n k i h hn) (hφ x n i hn)

theorem j_act_of (H : Realises K E P e T ρ j) (g : ↥(GK K)) (h : Hom P P)
    (hh : ∀ a, e (h.f a) = Per.σA (g : GQ l) (e a)) (x : E.M P) :
    j (E.tr h x) = TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (j x) := by
  obtain rfl := H.ainf.eq_galHom g h hh
  exact H.j_act g x

theorem end_ext (bc : SemiBC j) (s : WCb l ≃ₐ[ℤ_[l]] WCb l) {r r' : T →ₗ[ℤ_[l]] T}
    (h : ∀ x, TensorProduct.map s.toLinearMap r (j x) = TensorProduct.map s.toLinearMap r' (j x)) :
    r = r' := by
  have key : ∀ (r : T →ₗ[ℤ_[l]] T) (y : WCb l ⊗[ℤ_[l]] T),
      TensorProduct.map s.symm.toLinearMap LinearMap.id (TensorProduct.map s.toLinearMap r y) =
        r.baseChange (WCb l) y := fun r y => by
    induction y with
    | zero => simp
    | tmul a t => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  have h1 : r.baseChange (WCb l) = r'.baseChange (WCb l) :=
    bc.hom_ext fun x => by rw [← key, ← key, h]
  ext t
  apply one_tmul_injective (l := l) T
  simpa using LinearMap.congr_fun h1 (1 ⊗ₜ t)

theorem ρ_unique (H : Realises K E P e T ρ j) (H' : Realises K E P e T ρ' j) : ρ = ρ' :=
  funext fun g => end_ext H.bc (galW l (g : GQ l)) fun x => (H.j_act g x).symm.trans (H'.j_act g x)

theorem ρ_one (H : Realises K E P e T ρ j) : ρ 1 = LinearMap.id :=
  end_ext H.bc (galW l ((1 : ↥(GK K)) : GQ l)) fun x => by
    rw [← H.j_act_of 1 (Hom.id P) (fun a => (GlobalTheory.RingBasics.σA_one (e a)).symm), E.tr_id, OneMemClass.coe_one, map_one]
    exact (LinearMap.congr_fun TensorProduct.map_id _).symm

theorem ρ_mul (H : Realises K E P e T ρ j) (g h : ↥(GK K)) : ρ (g * h) = ρ g ∘ₗ ρ h :=
  end_ext H.bc (galW l ((g * h : ↥(GK K)) : GQ l)) fun x => by
    have h1 := H.j_act_of (g * h) ((H.ainf.galHom g).comp (H.ainf.galHom h))
      (fun a => by rw [← H.ainf.galHom_mul, H.ainf.e_galHom]) x
    rw [← h1, E.tr_comp, H.j_act, H.j_act, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
      Subgroup.coe_mul, map_mul]
    rfl

theorem finite (H : Realises K E P e T ρ j) : Module.Finite ℤ_[l] T := by
  have := E.fin P
  have := E.proj P
  have := H.bc.finite_projective.1
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (WCb l)

theorem free (H : Realises K E P e T ρ j) : Module.Free ℤ_[l] T := by
  have := E.fin P
  have := E.proj P
  have := H.bc.finite_projective.2
  have := H.finite
  have : Module.Flat (WCb l) (WCb l ⊗[ℤ_[l]] T) := Module.Flat.of_projective
  have : Module.Flat ℤ_[l] T := Module.Flat.of_flat_tensorProduct ℤ_[l] T (WCb l)
  exact Module.free_of_flat_of_isLocalRing

end Realises

def unitMap {K : FinExt l} (P : Obj l ↥(OL K)) (e : P.A ≃+* Ainf l) :
    (FCrys.unit l ↥(OL K)).M P →ₛₗ[(inclW l).comp e.toRingHom] (WCb l ⊗[ℤ_[l]] ℤ_[l]) :=
  (TensorProduct.AlgebraTensorModule.rid ℤ_[l] (WCb l) (WCb l)).symm.toLinearMap.comp
    ((inclW l).comp e.toRingHom).toSemilinearMap

theorem unitMap_apply {K : FinExt l} (P : Obj l ↥(OL K)) (e : P.A ≃+* Ainf l) (a : P.A) :
    unitMap P e a = inclW l (e a) ⊗ₜ[ℤ_[l]] (1 : ℤ_[l]) := rfl

theorem IsAinf.realises_unit {K : FinExt l} {P : Obj l ↥(OL K)} {e : P.A ≃+* Ainf l} (H : IsAinf K P e) :
    Realises K (FCrys.unit l ↥(OL K)) P e ℤ_[l] (fun _ => LinearMap.id) (unitMap P e) where
  ainf := H
  bc := (semiBC_self _).comp_equiv _
  j_φ d hd x m k h := by
    have : IsDomain P.A := e.toMulEquiv.isDomain
    have key : ∀ x m : P.A, m = (d : P.A) ^ k * P.D.φ x →
        inclW l (e d) ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id
          (inclW l (e x) ⊗ₜ[ℤ_[l]] (1 : ℤ_[l])) = inclW l (e m) ⊗ₜ[ℤ_[l]] (1 : ℤ_[l]) := by
      rintro x _ rfl
      have h3 : inclW l (e ((d : P.A) ^ k * P.D.φ x)) =
          inclW l (e d) ^ k * inclW l (WittVector.frobenius (e x)) := by
        rw [← H.e_φ]
        exact (map_mul ((inclW l).comp e.toRingHom) _ _).trans
          (congrArg (· * inclW l (e (P.D.φ x))) (map_pow ((inclW l).comp e.toRingHom) _ _))
      have h4 := h3.trans (congrArg (inclW l (e d) ^ k * ·) (frobW_inclW (e x)).symm)
      refine Eq.trans ?_ (congrArg (fun y : WCb l => y ⊗ₜ[ℤ_[l]] (1 : ℤ_[l])) h4.symm)
      rw [TensorProduct.map_tmul, TensorProduct.smul_tmul', smul_eq_mul, AlgHom.toLinearMap_apply,
        LinearMap.id_apply]
    exact key x m (eq_of_isFrac hd _ _ k h)
  j_act g x :=
    congrArg (fun y : WCb l => y ⊗ₜ[ℤ_[l]] (1 : ℤ_[l]))
      ((congrArg (inclW l) (H.e_galHom g x)).trans (galW_inclW _ _).symm)


example (K : FinExt l) : unitMap (ainfObj K) (ainfId K) (1 : Ainf l) ≠ 0 := fun h => by
  have h1 : (1 : WCb l) ⊗ₜ[ℤ_[l]] (1 : ℤ_[l]) = (1 : WCb l) ⊗ₜ[ℤ_[l]] (0 : ℤ_[l]) := by
    rw [TensorProduct.tmul_zero]
    exact (congrArg (fun y : WCb l => y ⊗ₜ[ℤ_[l]] (1 : ℤ_[l])) (map_one (inclW l)).symm).trans h
  exact one_ne_zero (one_tmul_injective (l := l) ℤ_[l] h1)

example (K : FinExt l) (ρ : ↥(GK K) → (ℤ_[l] →ₗ[ℤ_[l]] ℤ_[l]))
    (H : Realises K (FCrys.unit l ↥(OL K)) (ainfObj K) (ainfId K) ℤ_[l] ρ (unitMap _ _)) (g : ↥(GK K)) :
    ρ g = LinearMap.id :=
  congrFun (H.ρ_unique (isAinf_ainfObj K).realises_unit) g

example (K : FinExt l) (ρ : ↥(GK K) → (PUnit →ₗ[ℤ_[l]] PUnit)) :
    ¬ IsRealisation K (FCrys.unit l ↥(OL K)) PUnit ρ := by
  rintro ⟨j, H⟩
  obtain ⟨w, hw, -⟩ := H.bc (WCb l) ((inclW l).comp (ainfId K).toRingHom).toSemilinearMap
  have h := hw (1 : Ainf l)
  have h0 : ∀ y, w y = 0 := fun y => by rw [Subsingleton.elim y 0, map_zero]
  exact zero_ne_one (((h0 _).symm.trans h).trans (map_one (inclW l)))

example (K : FinExt l) : ((l : ℕ) : Ainf l) ∉ (ainfObj K).I := fun h => by
  have h1 : Per.θ l ((l : ℕ) : Ainf l) = 0 := h
  rw [map_natCast] at h1
  exact (Nat.cast_ne_zero.2 hl.out.ne_zero) h1

end GlobalTheory.Prism
end
end
