import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.Geo.Def.PC

section LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

abbrev SV (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

abbrev latA (Λ : Submodule (𝓞 E) (n → E)) : Submodule 𝒮 (n → 𝒜) := latS (F := F) 𝔸 𝒮 Λ

abbrev latV (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (SV E v) (n → E ⊗[F] v.adicCompletion F) := latS (F := F) (v.adicCompletion F) (SV E v) Λ

theorem pr_lat (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) (y : n → 𝒜)
    (hy : y ∈ latA (F := F) Λ) : (fun i => prV (E := E) v (y i)) ∈ latV v Λ := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    have : (fun i => prV (E := E) v ((0 : n → 𝒜) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => prV (E := E) v ((a + b) i)) =
        (fun i => prV (E := E) v (a i)) + (fun i => prV (E := E) v (b i)) := by ext i; simp
    rw [this]; exact add_mem ha hb
  | smul s a _ ha =>
    have : (fun i => prV (E := E) v ((s • a) i)) =
        (⟨prV (E := E) v (s : 𝒜), afsplit_prV_int v _ s.2⟩ : SV E v) • (fun i => prV (E := E) v (a i)) := by
      ext i
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ ha

theorem ie_lat (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E))
    (u : n → E ⊗[F] v.adicCompletion F) (hu : u ∈ latV v Λ) :
    (fun i => afsplitIE v (u i)) ∈ latA (F := F) Λ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    have : (fun i => afsplitIE v (inclE (F := F) (v.adicCompletion F) (x i))) =
        (⟨afsplitEps E v, afsplit_eps_int v⟩ : 𝒮) • (fun i => inclE (F := F) 𝔸 (x i)) := by
      ext i
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      rw [← afsplit_decomp, afsplit_prV_inclE]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  | zero =>
    have : (fun i => afsplitIE v ((0 : n → E ⊗[F] v.adicCompletion F) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => afsplitIE v ((a + b) i)) =
        (fun i => afsplitIE v (a i)) + (fun i => afsplitIE v (b i)) := by ext i; simp
    rw [this]; exact add_mem ha hb
  | smul s a _ ha =>
    have : (fun i => afsplitIE v ((s • a) i)) =
        (⟨afsplitIE v (s : E ⊗[F] v.adicCompletion F), afsplit_IE_int v _ s.2⟩ : 𝒮) •
          (fun i => afsplitIE v (a i)) := by
      ext i
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
    rw [this]; exact Submodule.smul_mem _ _ ha

theorem unit_away (D : 𝓞 F) (hD : D ≠ 0) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (u : 𝔸), u ∈ intAd F ∧
      (1 : 𝔸) = algebraMap (𝓞 F) 𝔸 D * u + ∑ v ∈ T, afsplitI v 1 := by
  classical
  have hmem : ∀ w : HeightOneSpectrum (𝓞 F),
      (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0
        else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹) ∈ w.adicCompletionIntegers F := by
    intro w
    split_ifs with h
    · exact zero_mem _
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
      have h1 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) ≤ 1 := levelaf_int_mem_v w D
      have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) = 1 := le_antisymm h1 (not_lt.1 h)
      rw [h2, inv_one]
  let u : 𝔸 := ⟨fun w => if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0
        else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹, Filter.Eventually.of_forall hmem⟩
  refine ⟨(levelaf_finite_places D hD).toFinset, u, hmem, ?_⟩
  refine FiniteAdeleRing.ext _ fun w => ?_
  have hsum : (∑ v ∈ (levelaf_finite_places D hD).toFinset, afsplitI v 1 : 𝔸) w =
      if w ∈ (levelaf_finite_places D hD).toFinset then 1 else 0 := by
    change evalV F w (∑ v ∈ (levelaf_finite_places D hD).toFinset, afsplitI v 1 : 𝔸) = _
    rw [map_sum]
    split_ifs with h
    · rw [Finset.sum_eq_single_of_mem w h]
      · exact afsplitI_self w 1
      · intro b _ hb; exact afsplitI_ne b w hb.symm 1
    · refine Finset.sum_eq_zero fun b hb => afsplitI_ne b w ?_ 1
      rintro rfl; exact h hb
  rw [afsplit_add_apply, afsplit_mul_apply, hsum]
  show (1 : w.adicCompletion F) = algebraMap (𝓞 F) (w.adicCompletion F) D *
    (if Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1 then 0
        else (algebraMap (𝓞 F) (w.adicCompletion F) D)⁻¹) + _
  by_cases h : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) D) < 1
  · have h' : w ∈ (levelaf_finite_places D hD).toFinset := by simpa using h
    rw [if_pos h, if_pos h', mul_zero, zero_add]
  · have h' : w ∉ (levelaf_finite_places D hD).toFinset := by simpa using h
    rw [if_neg h, if_neg h', add_zero, mul_inv_cancel₀ (levelaf_algebraMap_ne_zero w D hD)]

end LG

end Formalism.L2.Geo.Def.PC
end
end

section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P

namespace Formalism.L2.Geo.Def.PC

section LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem lg (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (y : n → 𝒜) (hy : ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (y i)) ∈ latV v Λ) :
    y ∈ latA (F := F) Λ := by
  classical
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  choose d0 hd0 hd0m using fun i => levelaf_denom (F := F) (E := E) (y i)
  have hE : ∀ v, (fun i => afsplitEps E v * y i) ∈ latA (F := F) Λ := by
    intro v
    have := ie_lat v Λ _ (hy v)
    simpa only [afsplit_decomp] using this
  have h3 : ∀ i, levelafC E (∏ j, d0 j) * y i ∈ 𝒮 := by
    intro i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm (d0 i), levelafC_mul, mul_assoc]
    exact mul_mem (levelafC_mem _) (hd0m i)
  have h4 := h₁ _ h3
  obtain ⟨T, u, hu, h1⟩ := unit_away (c₁ * ∏ j, d0 j)
    (mul_ne_zero hc₁ (Finset.prod_ne_zero_iff.2 fun j _ => hd0 j))
  have hu' : (1 : E) ⊗ₜ[F] u ∈ 𝒮 := Subring.subset_closure (Or.inr ⟨⟨u, hu⟩, rfl⟩)
  have hone : (1 : 𝒜) = ((1 : E) ⊗ₜ[F] u) * levelafC E (c₁ * ∏ j, d0 j) + ∑ v ∈ T, afsplitEps E v := by
    rw [Algebra.TensorProduct.one_def]
    conv_lhs => rw [h1]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_sum]
    congr 1
    rw [levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm u]
  have hy' : y = (⟨_, hu'⟩ : 𝒮) • (fun i => levelafC E c₁ * (levelafC E (∏ j, d0 j) * y i)) +
      ∑ v ∈ T, (fun i => afsplitEps E v * y i) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Subring.smul_def, smul_eq_mul]
    conv_lhs => rw [← one_mul (y i), hone]
    rw [levelafC_mul, add_mul, Finset.sum_mul]
    ring
  rw [hy']
  exact add_mem (Submodule.smul_mem _ _ h4) (sum_mem fun v _ => hE v)

omit [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in
theorem mem_stab_of {A R : Type} [CommRing A] [CommRing R] [Algebra R A] (Λ : Submodule R (n → A)) (g : GL n A)
    (h1 : ∀ x ∈ Λ, (g : Matrix n n A) *ᵥ x ∈ Λ)
    (h2 : ∀ x ∈ Λ, ((g⁻¹ : GL n A) : Matrix n n A) *ᵥ x ∈ Λ) : g ∈ stabGL Λ := by
  unfold stabGL
  refine fun x => ⟨h1 x, fun hx => ?_⟩
  have h3 := h2 _ hx
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h3

theorem pr_mulVec (v : HeightOneSpectrum (𝓞 F)) (x : GL n 𝒜) (y : n → 𝒜) :
    (fun i => prV (E := E) v (((x : Matrix n n 𝒜) *ᵥ y) i)) =
      ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ
        (fun i => prV (E := E) v (y i)) := by
  unfold prV bc
  funext i
  rw [Units.coe_map]
  exact RingHom.map_mulVec _ _ _ i

private theorem prV_inclE' (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) 𝔸 e) = inclE (F := F) (v.adicCompletion F) e := by
  simp [prV, inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul]

private theorem stabGL_latA_pr_of_mem (Λ : Submodule (𝓞 E) (n → E)) (x : GL n 𝒜)
    (hx : x ∈ stabGL (latA (F := F) Λ)) (v : HeightOneSpectrum (𝓞 F)) (z : n → E ⊗[F] v.adicCompletion F)
    (hz : z ∈ latV v Λ) :
    ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
      latV v Λ := by
  have hx' : ∀ y : n → 𝒜, y ∈ latA (F := F) Λ ↔ (x : Matrix n n 𝒜) *ᵥ y ∈ latA (F := F) Λ := hx
  unfold latV latS at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have hmem : (fun i => inclE (F := F) 𝔸 (l i)) ∈ latA (F := F) Λ :=
      Submodule.subset_span ⟨l, hl, rfl⟩
    have h2 := pr_lat (F := F) v Λ _ ((hx' _).1 hmem)
    rw [pr_mulVec] at h2
    have e : (fun i => prV (E := E) v (inclE (F := F) 𝔸 (l i))) =
        (fun i => inclE (F := F) (v.adicCompletion F) (l i)) := funext fun i => prV_inclE' v (l i)
    rw [e] at h2
    exact h2
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul s a _ ha =>
    have e : ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ (s • a) =
        s • (((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ a) := by
      funext i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    exact Submodule.smul_mem _ s ha

theorem stab_pr (Λ : Submodule (𝓞 E) (n → E)) (x : GL n 𝒜) (hx : x ∈ stabGL (latA (F := F) Λ))
    (v : HeightOneSpectrum (𝓞 F)) : bc (prV (E := E) v) x ∈ stabGL (latV v Λ) := by
  have hxi : x⁻¹ ∈ stabGL (latA (F := F) Λ) := inv_mem hx
  have key : ∀ z : n → E ⊗[F] v.adicCompletion F, z ∈ latV v Λ ↔
      ((bc (prV (E := E) v) x : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈ latV v Λ := by
    intro z
    refine ⟨stabGL_latA_pr_of_mem Λ x hx v z, fun hz => ?_⟩
    have h := stabGL_latA_pr_of_mem Λ x⁻¹ hxi v _ hz
    rwa [map_inv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h
  exact key

theorem stab_of_loc (Λ : Submodule (𝓞 E) (n → E)) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (x : GL n 𝒜) (hx : ∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) x ∈ stabGL (latV v Λ)) :
    x ∈ stabGL (latA (F := F) Λ) := by
  have fwd : ∀ g : GL n 𝒜, (∀ v : HeightOneSpectrum (𝓞 F), bc (prV (E := E) v) g ∈ stabGL (latV v Λ)) →
      ∀ y ∈ latA (F := F) Λ, (g : Matrix n n 𝒜) *ᵥ y ∈ latA (F := F) Λ := by
    intro g hg y hy
    refine lg (F := F) Λ hspan _ fun v => ?_
    rw [pr_mulVec]
    have hgv : ∀ z : n → E ⊗[F] v.adicCompletion F, z ∈ latV v Λ ↔
        ((bc (prV (E := E) v) g : GL n (E ⊗[F] v.adicCompletion F)) :
          Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈ latV v Λ := hg v
    exact (hgv _).1 (pr_lat (F := F) v Λ y hy)
  refine mem_stab_of (latA (F := F) Λ) x (fwd x hx) (fwd x⁻¹ fun v => ?_)
  rw [map_inv]
  exact inv_mem (hx v)


end LG

end Formalism.L2.Geo.Def.PC
end
end
