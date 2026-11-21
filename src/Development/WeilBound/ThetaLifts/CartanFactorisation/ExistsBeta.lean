import Development.WeilBound.ThetaLifts.CartanFactorisation.SpanOrbitStab
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA

section
noncomputable section

namespace PositivityTheory.ThKF

open scoped InnerProductSpace
open Abs

section

variable {Q : Type} [AddCommGroup Q] [Module ℂ Q] (β : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ)

theorem rad_of_zero (hs : ∀ x y, β x y = starRingEnd ℂ (β y x)) (hp : ∀ x, 0 ≤ (β x x).re) {x : Q} (h : β x x = 0) :
    β x = 0 := by
  let c : PreInnerProductSpace.Core ℂ Q :=
    { inner := fun x y => β x y
      conj_inner_symm := fun x y => (hs x y).symm
      re_inner_nonneg := hp
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  ext y
  have := InnerProductSpace.Core.inner_mul_inner_self_le (c := c) x y
  change ‖β x y‖ * ‖β y x‖ ≤ RCLike.re (β x x) * RCLike.re (β y y) at this
  rw [h, map_zero, zero_mul, hs y x, RCLike.norm_conj] at this
  have h2 : ‖β x y‖ = 0 := by nlinarith [norm_nonneg (β x y)]
  simpa using h2

def QR : Type := Q ⧸ LinearMap.ker β

instance : AddCommGroup (QR β) := inferInstanceAs (AddCommGroup (Q ⧸ LinearMap.ker β))
instance : Module ℂ (QR β) := inferInstanceAs (Module ℂ (Q ⧸ LinearMap.ker β))

def mkR : Q →ₗ[ℂ] QR β := (LinearMap.ker β).mkQ

theorem mkR_surj : Function.Surjective (mkR β) := (LinearMap.ker β).mkQ_surjective

theorem mkR_eq_zero {x : Q} : mkR β x = 0 ↔ β x = 0 := Submodule.Quotient.mk_eq_zero _

theorem ex_form (hs : ∀ x y, β x y = starRingEnd ℂ (β y x)) :
    ∃ b : QR β → QR β → ℂ, ∀ x y, b (mkR β x) (mkR β y) = β x y := by
  refine ⟨fun u v => β (mkR_surj β u).choose (mkR_surj β v).choose, fun x y => ?_⟩
  have e : ∀ x, β (mkR_surj β (mkR β x)).choose = β x := fun x => by
    rw [← sub_eq_zero, ← map_sub, ← mkR_eq_zero, map_sub, (mkR_surj β (mkR β x)).choose_spec, sub_self]
  show β _ _ = _
  rw [e x, hs, e y, ← hs]

theorem ex_desc (A : Module.End ℂ Q) (h : ∀ x, β x = 0 → β (A x) = 0) :
    ∃ A' : Module.End ℂ (QR β), ∀ x, A' (mkR β x) = mkR β (A x) :=
  ⟨(LinearMap.ker β).mapQ (LinearMap.ker β) A fun x hx => h x hx, fun _ => rfl⟩

end

theorem absUnit : AbsUnit := by
  intro Q _ _ β 𝒪 A₀ hs hp h0 hadj hadm N hN huniq
  classical
  obtain ⟨b, hb⟩ := ex_form β hs
  have sj := mkR_surj β
  let c : InnerProductSpace.Core ℂ (QR β) :=
    { inner := b
      conj_inner_symm := fun x y => by obtain ⟨x, rfl⟩ := sj x; obtain ⟨y, rfl⟩ := sj y; rw [hb, hb]; exact (hs x y).symm
      re_inner_nonneg := fun x => by obtain ⟨x, rfl⟩ := sj x; rw [hb]; exact hp x
      add_left := fun x y z => by
        obtain ⟨x, rfl⟩ := sj x; obtain ⟨y, rfl⟩ := sj y; obtain ⟨z, rfl⟩ := sj z
        rw [← map_add, hb, hb, hb]; simp
      smul_left := fun x y r => by
        obtain ⟨x, rfl⟩ := sj x; obtain ⟨y, rfl⟩ := sj y
        rw [← map_smul, hb, hb]; simp
      definite := fun x hx => by
        obtain ⟨x, rfl⟩ := sj x
        rw [hb] at hx
        exact (mkR_eq_zero β).2 (rad_of_zero β hs hp hx) }
  letI : NormedAddCommGroup (QR β) := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (QR β) := InnerProductSpace.ofCore c.toCore
  have hin : ∀ x y, ⟪mkR β x, mkR β y⟫_ℂ = β x y := hb
  have hrad : ∀ A ∈ 𝒪, ∀ x, β x = 0 → β (A x) = 0 := fun A hA x hx => by
    obtain ⟨A', -, c, h⟩ := hadj A hA
    ext y; simp [h, hx]
  have hA₀ : ∀ x ∈ A₀, mkR β x = 0 := fun x hx => (mkR_eq_zero β).2 (rad_of_zero β hs hp (h0 x hx))
  let St : Submodule ℂ (QR β) → Prop := fun S => ∀ A ∈ 𝒪, ∀ x, mkR β x ∈ S → mkR β (A x) ∈ S
  have hproj : Proj St := by
    intro u
    obtain ⟨f, rfl⟩ := sj u
    obtain ⟨K, _, κ, hκ, hiso, hfin, hhom⟩ := hadm f
    choose D hD using fun k => ex_desc β (κ k) (hrad _ (hκ k))
    let κ' : K →* Module.End ℂ (QR β) :=
      { toFun := D
        map_one' := LinearMap.ext fun u => by obtain ⟨x, rfl⟩ := sj u; simp [hD]
        map_mul' := fun k k' => LinearMap.ext fun u => by obtain ⟨x, rfl⟩ := sj u; simp [hD] }
    have hκ' : ∀ k x, κ' k (mkR β x) = mkR β (κ k x) := hD
    have hi : ∀ k x y, ⟪κ' k x, κ' k y⟫_ℂ = ⟪x, y⟫_ℂ := fun k x y => by
      obtain ⟨x, rfl⟩ := sj x; obtain ⟨y, rfl⟩ := sj y; rw [hκ', hκ', hin, hin, hiso]
    have hf : ∀ u, FiniteDimensional ℂ (orb κ' u) := fun u => by
      obtain ⟨x, rfl⟩ := sj u
      obtain ⟨t, ht⟩ := hfin x
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (t : Set Q)).map (mkR β)) (Submodule.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      obtain ⟨y, hy, z, hz, e⟩ := Submodule.mem_sup.1 (ht k)
      exact ⟨y, hy, by show _ = κ' k _; rw [hκ', ← e, map_add, hA₀ z hz, add_zero]⟩
    have := hf (mkR β f)
    let W := orb κ' (mkR β f)
    let bs : W ≃ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun
    let r : K → Module.End ℂ W := fun k => (κ' k).restrict (span_orbit_stab κ' (mkR β f) k)
    let ρ : K →* Module.End ℂ (Fin (Module.finrank ℂ W) → ℂ) :=
      { toFun := fun k => bs.toLinearMap ∘ₗ r k ∘ₗ bs.symm.toLinearMap
        map_one' := LinearMap.ext fun y => by
          have : r 1 (bs.symm y) = bs.symm y := Subtype.ext (by show κ' 1 _ = _; simp)
          simp [this]
        map_mul' := fun k k' => LinearMap.ext fun y => by
          have : r (k * k') (bs.symm y) = r k (r k' (bs.symm y)) := Subtype.ext (by show κ' (k * k') _ = κ' k (κ' k' _); simp)
          simp [this] }
    obtain ⟨t, ht⟩ := hhom _ ρ fun hfix k => LinearMap.ext fun y => by
      have h1 : ∀ w ∈ W, κ' k w = w := fun w hw => by
        induction hw using Submodule.span_induction with
        | mem y h => obtain ⟨k', rfl⟩ := h; simp only [hκ', hfix]
        | zero => simp
        | add a b _ _ ha hb => rw [map_add, ha, hb]
        | smul c a _ ha => rw [map_smul, ha]
      have : r k (bs.symm y) = bs.symm y := Subtype.ext (h1 _ (bs.symm y).2)
      show bs (r k (bs.symm y)) = y
      simp [this]
    have hH : FiniteDimensional ℂ (homs κ' W) := by
      let j : homs κ' W →ₗ[ℂ] Submodule.span ℂ (t : Set (Q →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ))) :=
        { toFun := fun L => ⟨bs.toLinearMap ∘ₗ (L.1.codRestrict W L.2.1) ∘ₗ mkR β, ht _
            (fun x hx => by simp [hA₀ x hx]) fun k x => by
              show bs _ = bs (r k (bs.symm (bs _)))
              rw [bs.symm_apply_apply]
              exact congrArg bs (Subtype.ext (by show L.1 (mkR β (κ k x)) = κ' k (L.1 (mkR β x)); rw [← hκ', L.2.2]))⟩
          map_add' := fun a b => Subtype.ext (LinearMap.ext fun x => bs.map_add ⟨_, a.2.1 _⟩ ⟨_, b.2.1 _⟩)
          map_smul' := fun c a => Subtype.ext (LinearMap.ext fun x => bs.map_smul c ⟨_, a.2.1 _⟩) }
      refine Module.Finite.of_injective j ((injective_iff_map_eq_zero j).2 fun L hL => Subtype.ext (LinearMap.ext fun u => ?_))
      obtain ⟨x, rfl⟩ := sj u
      have h1 : bs ⟨L.1 (mkR β x), L.2.1 _⟩ = 0 := LinearMap.congr_fun (congrArg Subtype.val hL) x
      exact congrArg Subtype.val (bs.map_eq_zero_iff.1 h1)
    obtain ⟨Z, Z', h1, h2, h3, h4⟩ := exists_e κ' hi hf _ hH
    refine ⟨Z, Z', h1, h2, h3, fun S hS => h4 S fun k y hy => ?_⟩
    obtain ⟨x, rfl⟩ := sj y
    rw [hκ']
    exact hS _ (hκ k) x hy
  have hbot := eq_bot hproj (fun s hs A hA x hx => Submodule.mem_sInf.2 fun S hS => hs S hS A hA x (Submodule.mem_sInf.1 hx S hS))
    (fun S hS A hA x hx => by
      obtain ⟨A', hA', c, h⟩ := hadj A hA
      rw [Submodule.mem_orthogonal']
      intro u hu
      obtain ⟨y, rfl⟩ := sj u
      rw [hin, h, ← hin, (Submodule.mem_orthogonal' _ _).1 hx _ (hS A' hA' y hu), mul_zero])
    (N.map (mkR β)) (fun A hA x hx => by
      obtain ⟨y, hy, e⟩ := hx
      refine ⟨A y, hN.prop.1.2 A hA y hy, ?_⟩
      rw [← sub_eq_zero, ← map_sub, ← map_sub, mkR_eq_zero]
      exact hrad A hA _ ((mkR_eq_zero β).1 (by rw [map_sub, e, sub_self])))
    fun M hM => by
      have : M.comap (mkR β) = N := huniq _ ⟨⟨⟨fun x hx => by simp [hA₀ x hx], fun A hA x hx => hM.prop.1 A hA x hx⟩,
        fun ht => hM.prop.2 (eq_top_iff.2 fun u _ => by obtain ⟨x, rfl⟩ := sj u; exact (ht ▸ Submodule.mem_top : x ∈ M.comap (mkR β)))⟩,
        fun P hP hle => by
          have hk : ∀ x y, y ∈ P → mkR β y = mkR β x → x ∈ P := fun x y hy e => by
            have : x - y ∈ P := hle (show mkR β (x - y) ∈ M by rw [map_sub, e, sub_self]; exact M.zero_mem)
            simpa using P.add_mem this hy
          have h1 : P.map (mkR β) ≤ M := hM.le_of_ge ⟨fun A hA x ⟨y, hy, e⟩ => ⟨A x, hP.1.2 A hA x (hk x y hy e), rfl⟩,
            fun ht => hP.2 (eq_top_iff.2 fun x _ => by
              obtain ⟨y, hy, e⟩ : mkR β x ∈ P.map (mkR β) := ht ▸ Submodule.mem_top
              exact hk x y hy e)⟩ fun u hu => by obtain ⟨x, rfl⟩ := sj u; exact ⟨x, hle hu, rfl⟩
          exact fun x hx => h1 ⟨x, hx, rfl⟩⟩
      rw [← this]
      exact Submodule.map_comap_le _ _
  intro x hx
  have : mkR β x = 0 := (Submodule.eq_bot_iff _).1 hbot _ ⟨x, hx, rfl⟩
  simp [(mkR_eq_zero β).1 this]

end PositivityTheory.ThKF

end
end

section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def AdmAt (om : Rep σ X W) (v : Pl F) : Prop :=
  ∀ U ∈ 𝓝 (1 : UA σ W.J), ∃ t : Finset (((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
    ∀ l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ, augAt om v ≤ LinearMap.ker l →
      (∀ h ∈ U, h ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → l φ₁ = l φ) →
      ∃ l' ∈ Submodule.span ℂ (t : Set (((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ)), ∀ φ ∈ SB _, l φ = l' φ

end PositivityTheory.ThKF

end
end

section
noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped ComplexConjugate

theorem maximal_of {Q P : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup P] [Module ℂ P] [Nontrivial P] (p : Q →ₗ[ℂ] P)
    (S : Submodule ℂ Q) (St : Submodule ℂ Q → Prop) (onto : S.map p = ⊤) (hle : ∀ N, St N → N ≤ S)
    (h0 : St (LinearMap.ker p ⊓ S)) (hirr : ∀ N, St N → N.map p = ⊥ ∨ N.map p = ⊤) :
    Maximal (fun N => St N ∧ N ≠ S) (LinearMap.ker p ⊓ S) := by
  refine ⟨⟨h0, fun e => ?_⟩, fun N hN hge x hx => ?_⟩
  · have : (⊤ : Submodule ℂ P) = ⊥ := by
      rw [← onto, ← e, eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    exact top_ne_bot this
  · rcases hirr N hN.1 with h | h
    · exact ⟨(Submodule.eq_bot_iff _).1 h _ ⟨x, hx, rfl⟩, hle N hN.1 hx⟩
    · refine absurd (le_antisymm (hle N hN.1) fun y hy => ?_) hN.2
      obtain ⟨z, hz, e⟩ : p y ∈ N.map p := h ▸ Submodule.mem_top
      have : y - z ∈ N := hge ⟨by simp [e], sub_mem hy (hle N hN.1 hz)⟩
      simpa using N.add_mem this hz

theorem max_comap {Q : Type} [AddCommGroup Q] [Module ℂ Q] (S : Submodule ℂ Q) (St : Submodule ℂ Q → Prop)
    (St' : Submodule ℂ S → Prop) (hle : ∀ N, St N → N ≤ S) (h : ∀ P : Submodule ℂ S, St' P ↔ St (P.map S.subtype))
    (N : Submodule ℂ Q) (hN : Maximal (fun N => St N ∧ N ≠ S) N) (hu : ∀ N', Maximal (fun N => St N ∧ N ≠ S) N' → N' = N) :
    Maximal (fun P => St' P ∧ P ≠ ⊤) (N.comap S.subtype) ∧
      ∀ P, Maximal (fun P => St' P ∧ P ≠ ⊤) P → P = N.comap S.subtype := by
  have mc : ∀ N, N ≤ S → (N.comap S.subtype).map S.subtype = N := fun N hN => by
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hN]
  have inj := Submodule.map_injective_of_injective S.injective_subtype
  have ne : ∀ P : Submodule ℂ S, P ≠ ⊤ ↔ P.map S.subtype ≠ S := fun P => by
    constructor
    · intro h e; exact h (inj (e.trans (Submodule.map_subtype_top S).symm))
    · intro h e; exact h (e ▸ Submodule.map_subtype_top S)
  refine ⟨⟨⟨(h _).2 (by rw [mc N (hle N hN.prop.1)]; exact hN.prop.1), (ne _).2 (by rw [mc N (hle N hN.prop.1)]; exact hN.prop.2)⟩,
    fun P hP hge x hx => hN.le_of_ge ⟨(h P).1 hP.1, (ne P).1 hP.2⟩
      ((mc N (hle N hN.prop.1)).symm.le.trans (Submodule.map_mono hge)) ⟨x, hx, rfl⟩⟩, fun P hP => ?_⟩
  have := hu (P.map S.subtype) ⟨⟨(h P).1 hP.prop.1, (ne P).1 hP.prop.2⟩, fun N' hN' hge => by
    have h1 : N'.comap S.subtype ≤ P := hP.le_of_ge ⟨(h _).2 (by rw [mc N' (hle N' hN'.1)]; exact hN'.1),
      (ne _).2 (by rw [mc N' (hle N' hN'.1)]; exact hN'.2)⟩ (Submodule.map_le_iff_le_comap.1 hge)
    exact (mc N' (hle N' hN'.1)).symm.le.trans (Submodule.map_mono h1)⟩
  rw [← this, Submodule.comap_map_eq_of_injective S.injective_subtype]

theorem exists_beta {G : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] (𝓕 : Set G) (μ : Measure G)
    {Q : Type} [AddCommGroup Q] [Module ℂ Q] (u : Q →ₗ[ℂ] (G → ℂ)) (hc : ∀ x, Continuous (u x))
    (h2 : ∀ x, IntegrableOn (fun g => ‖u x g‖ ^ 2) 𝓕 μ) :
    ∃ β : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ, (∀ x y, β x y = ∫ g in 𝓕, conj (u x g) * u y g ∂μ) ∧
      (∀ x y, β x y = starRingEnd ℂ (β y x)) ∧ ∀ x, 0 ≤ (β x x).re := by
  have ii := fun x y => L2.integrableOn_mul (hc x) (hc y) (h2 x) (h2 y)
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ g in 𝓕, conj (u x g) * u y g ∂μ)
    (fun x x' y => ?_) (fun c x y => ?_) (fun x y y' => ?_) (fun c x y => ?_), fun _ _ => rfl, fun x y => ?_, fun x => ?_⟩
  · rw [← integral_add (ii x y) (ii x' y)]; simp [add_mul]
  · simp [← integral_const_mul, mul_assoc]
  · rw [← integral_add (ii x y) (ii x y')]; simp [mul_add]
  · simp [← integral_const_mul, mul_left_comm]
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [← integral_conj]; simp [mul_comm]
  · simp only [LinearMap.mk₂'ₛₗ_apply]
    rw [← RCLike.re_to_complex, ← integral_re (ii x x)]
    exact integral_nonneg fun g => by
      simp only [Complex.conj_mul', Pi.zero_apply, RCLike.re_to_complex, ← Complex.ofReal_pow, Complex.ofReal_re]; positivity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def LocCpt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (X : Spc F E n)
    (v : Pl F), (∀ g ∈ UAt σ X (evFin F v), g⁻¹ ∈ UAt σ X (evFin F v)) ∧
      (∀ g ∈ UAt σ X (evFin F v), ∀ g' ∈ UAt σ X (evFin F v), g * g' ∈ UAt σ X (evFin F v)) ∧ ∀ U ∈ 𝓝 (1 : UA σ X.J),
      ∃ K : Subgroup (UA σ X.J), IsCompact (K : Set (UA σ X.J)) ∧ (K : Set (UA σ X.J)) ⊆ U ∩ UAt σ X (evFin F v) ∧
        ∃ U' ∈ 𝓝 (1 : UA σ X.J), U' ∩ UAt σ X (evFin F v) ⊆ K

def KInfGrp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (X : Spc F E n)
    (τ : ∀ w : InfinitePlace F, EmbOver E w), ∃ K : Subgroup (UA σ X.J), (K : Set (UA σ X.J)) = KInf σ X τ

structure Cls (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (𝓒 : Submodule ℂ (Fn F n d)) : Prop where
  sch : 𝓒 ≤ schA F _
  conv : ∀ Φ ∈ 𝓒, M.Conv om Φ
  cont : ∀ Φ ∈ 𝓒, Continuous (M.I om Φ)
  contf : ∀ ψ ∈ SB (Fin n × Fin d → Af F), (∀ f : SInf F (Fin n × Fin d), pureA F f ψ ∈ 𝓒) →
    ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f ψ) h
  sq : ∀ (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
    ∀ Φ ∈ 𝓒, Φ ∈ PolData B M → IntegrableOn (fun h => ‖M.I om Φ h‖ ^ 2) 𝓕 μ

section I

variable {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem I_add' (hp : IsPair B M χX χW om r s r' s') {𝓒} (hc : Cls B M om 𝓒) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ 𝓒) (hΨ : Ψ ∈ 𝓒) :
    M.I om (Φ + Ψ) = M.I om Φ + M.I om Ψ := by
  funext h
  have e : ∀ g, theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := fun g => by
    simp only [theta, map_add]
    exact thetaSum_add F (hp.weil.isUSplitting.pres _ _ (hc.sch hΦ)) (hp.weil.isUSplitting.pres _ _ (hc.sch hΨ))
  simp only [Model.I, e, Pi.add_apply]
  exact integral_add (hc.conv _ hΦ h) (hc.conv _ hΨ h)

theorem I_right (Φ : Fn F n d) (h₀ h : UA σ W.J) : M.I om (om (1, h₀) Φ) h = M.I om Φ (h * h₀) := by
  simp only [Model.I, theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem det_of_sig {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} {r s : ℕ} (h : HasSig A r s) : A.det ≠ 0 := by
  obtain ⟨e, P, hP⟩ := h
  have h1 : Pᵀ * (A * (P.map star * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ))) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP, Matrix.fromBlocks_multiply]; simp
  rw [Matrix.mul_eq_one_comm_of_equiv (finSumFinEquiv.trans (finCongr e)), Matrix.mul_assoc] at h1
  exact (Matrix.isUnit_det_of_right_inverse h1).ne_zero

theorem detX (hp : IsPair B M χX χW om r s r' s') : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine det_of_sig (hp.herm.sig w) ?_
  rw [show X.J.map (B.emb w).1 = (RingHom.mapMatrix ((B.emb w).1 : E →+* ℂ)) X.J from rfl, ← RingHom.map_det, h0, map_zero]

theorem detW (hp : IsPair B M χX χW om r s r' s') : W.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine det_of_sig (hp.skew.sig w) ?_
  rw [Matrix.det_smul, show W.J.map (B.emb w).1 = (RingHom.mapMatrix ((B.emb w).1 : E →+* ℂ)) W.J from rfl, ← RingHom.map_det, h0,
    map_zero, mul_zero]

theorem uniX (hU : Unimod) (hp : IsPair B M χX χW om r s r' s') : Countable (ratU σ X.J) ∧ M.μ.IsMulRightInvariant := by
  obtain ⟨h1, -, h3⟩ := hU F E σ hp.base.cm n X.J 1 (fun i j => by simpa using hp.herm.herm i j) (detX hp)
  exact ⟨h1, h3 _ hp.good.haar⟩

theorem uniW (hU : Unimod) (hp : IsPair B M χX χW om r s r' s') : Countable (ratU σ W.J) ∧
    ∃ (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), μ.IsHaarMeasure ∧ IsFundamentalDomain (ratU σ W.J) 𝓕 μ ∧
      μ.IsMulRightInvariant := by
  obtain ⟨h1, ⟨μ, 𝓕, h2, h2'⟩, h3⟩ := hU F E σ hp.base.cm d W.J (-1) (fun i j => by simpa using hp.skew.skew i j) (detW hp)
  exact ⟨h1, μ, 𝓕, h2, h2', h3 _ h2⟩

theorem I_left (hU : Unimod) (hT : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (g₀ : UA σ X.J) : M.I om (om (g₀, 1) Φ) = M.I om Φ := by
  funext h
  obtain ⟨h1, h2⟩ := uniX hU hp
  haveI := hp.good.haar
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have e : ∀ g, theta om (om (g₀, 1) Φ) g h = theta om Φ (g * g₀) h := fun g => by
    simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [Model.I, e]
  exact L2.integral_right hp.good.dom (fun g => theta om Φ g h) (fun γ hγ g => by
    simpa using ((hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1 γ hγ 1 (one_mem _) g h) g₀

theorem I_inv (hT : ThetaBasic) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) :
    L2.Inv (ratU σ W.J) (M.I om Φ) := fun γ hγ h => by
  simp only [Model.I]
  congr 1
  funext g
  simpa using ((hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ).2.1 1 (one_mem _) γ hγ g h

end I

end PositivityTheory.ThKF

end
end
