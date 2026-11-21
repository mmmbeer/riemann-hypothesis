import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCW
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilEq
import Formalism.LocalToGlobal.BesselHermitianTheta.BesselUnipotentSubgroup
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
import Formalism.LocalToGlobal.JointCharacters.TauEEqEmbTau

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.Inhab Formalism.BasicNotions.Examples₂

variable {D : D7}

theorem xs_fits (R : Ranks) (t j : ℕ) (hj : j < R.m) : R.k + j * (t + 1) ≤ R.r + j * t - (R.m - j) / 2 := by
  have h1 : j * (t + 1) = j * t + j := by ring
  rw [h1]
  generalize j * t = s
  unfold Ranks.r
  omega

theorem nu_le (R : Ranks) (t j : ℕ) : (R.m - j) / 2 ≤ R.r + j * t := by
  have hk := R.m_add_three_le_k
  have : (R.m - j) / 2 ≤ R.r := by unfold Ranks.r; omega
  omega

def sigTow (D : D7) (t : ℕ) : Tow D t where
  Xs := fun j => posSpace star_isIntegral (D.R.k + j * (t + 1))
  Xs_rank := fun _ _ => rfl
  Xs_sig := fun _ _ => ⟨posSpace_sigOK _ _, fun _ => Or.inl rfl⟩
  Ys := fun j => dSpace star_isIntegral (D.R.r + j * t) ((D.R.m - j) / 2)
  Ys_rank := fun _ _ => rfl
  Ys_sig := fun j _ => dSpace_sigOK _ _ _ (nu_le D.R t j)
  iXYs := fun _ => extLE _ _
  iXYs_isom := fun j hj x y => extLE_isom _ _ ((xs_fits D.R t j hj).trans (Nat.sub_le _ _)) _ _
    (fun i => negTail_false _ _ _ (lt_of_lt_of_le i.isLt (xs_fits D.R t j hj))) x y
  iYXm := extLE _ _
  iYXm_isom := fun x y => extLE_isom _ _ (by
      have := D.R.two_le_m
      unfold Ranks.r
      rw [Nat.mul_succ]
      omega) _ _ (fun i => (negTail_false _ _ _ (by have := i.isLt; omega)).symm) x y

open Classical in

def towC (D : D7) (t : ℕ) : Tow D t := if h : t = D.R.t then h ▸ recTow D else sigTow D t

theorem towC_rec (D : D7) : towC D D.R.t = recTow D := by
  unfold towC
  rw [dif_pos rfl]

def SpSig (D : D7) : Prop :=
  ∀ j, j ≤ D.R.m → (D.sp.X j).IsPosDef ∧
    ∀ τ, (D.sp.Y j).sig τ = (D.R.r + j * D.R.t - (D.R.m - j) / 2, (D.R.m - j) / 2)

theorem towC_sig (h : SpSig D) (t j : ℕ) (hj : j ≤ D.R.m) : ((towC D t).Xs j).IsPosDef ∧
    ∀ τ, ((towC D t).Ys j).sig τ = (D.R.r + j * t - (D.R.m - j) / 2, (D.R.m - j) / 2) := by
  by_cases e : t = D.R.t
  · subst e
    rw [towC_rec]
    exact h j hj
  · unfold towC
    rw [dif_neg e]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem towC_ok (t j : ℕ) : ((towC D t).Ys j).SigOK := by
  by_cases e : t = D.R.t
  · subst e
    rw [towC_rec]
    exact D.sp.Y_sig j
  · unfold towC
    rw [dif_neg e]
    exact dSpace_sigOK star_isIntegral _ _ (nu_le D.R t j)

def WittLow (D : D7) : Prop := ∀ (V : HSp D) (i : ℕ), (∃ C : Matrix (Fin V.rank) (Fin i) D.host.E, IsIsoSub V C) →
  ∃ V' : HSp D, IsWittLower V V' i

open Classical in

def lowC (V : HSp D) (i : ℕ) : HSp D :=
  if i = 0 then V else if h : ∃ V' : HSp D, IsWittLower V V' i then fixSig h.choose else V

theorem lowC_spec (hW : WittLow D) (V : HSp D) (hV : V.SigOK) (i : ℕ)
    (h : ∃ C : Matrix (Fin V.rank) (Fin i) D.host.E, IsIsoSub V C) : IsWittLower V (lowC V i) i ∧ (lowC V i).SigOK := by
  unfold lowC
  by_cases e : i = 0
  · subst e
    rw [if_pos rfl]
    obtain ⟨C, hC⟩ := h
    exact ⟨⟨rfl, LinearMap.id, fun _ _ => rfl, C, hC, Subsingleton.elim _ _⟩, hV⟩
  · have h' := hW V i h
    rw [if_neg e, dif_pos h']
    exact ⟨h'.choose_spec, fixSig_ok _⟩

def EmbU (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ g g' h, EmbRel A B ι g h → EmbRel A B ι g' h → g = g'

def EmbRat (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ γ ∈ GQ B, ∃ γ' ∈ GQ A, EmbRel A B ι γ' γ

theorem embRel_mul {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} {g g' : GA D A} {h h' : GA D B} (a : EmbRel A B ι g h)
    (b : EmbRel A B ι g' h') : EmbRel A B ι (g * g') (h * h') := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, b.1, ← Matrix.mul_assoc, a.1, Matrix.mul_assoc]
  · rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, b.2 x hx, a.2 x hx]

def EmbCond (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : Prop :=
  HSpace.IsIsomEmb B A ι ∧ ∃ s : GA D B → GA D A, ∀ h, EmbRel A B ι (s h) h

def embC {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : EmbCond A B ι) : GA D B → GA D A := h.2.choose

theorem embC_spec {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : EmbCond A B ι) (x : GA D B) : EmbRel A B ι (embC h x) x :=
  h.2.choose_spec x

theorem embC_left (hU : EmbU D) (hR : EmbRat D) {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : EmbCond A B ι)
    {γ : GA D B} (hγ : γ ∈ GQ B) : ∃ γ' ∈ GQ A, EmbRel A B ι γ' γ ∧ ∀ x, embC h (γ * x) = γ' * embC h x := by
  obtain ⟨γ', a, b⟩ := hR A B ι h.1 γ hγ
  exact ⟨γ', a, b, fun x => hU A B ι h.1 _ _ _ (embC_spec h _) (embRel_mul b (embC_spec h x))⟩

def TopInt (D : D7) : Prop := ∀ (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V), HSpace.IsIsomEmb B A ι →
  ∀ s : GA D B → GA D A, (∀ h, EmbRel A B ι (s h) h) →
  ∀ (μ : Measure (GA D B)) (𝓕 : Set (GA D B)), μ.IsHaarMeasure → IsFundamentalDomain (GQ B) 𝓕 μ →
  ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFunSm (th0 D) A φ → IsAutFunSm (th0 D) B F → IsCuspFun B F →
    IntegrableOn (fun h => star (φ (s h)) * F h) 𝓕 μ

open Classical in

def btopC (petF : HSp D → ℝ) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) (φ : afC D A) (F : cuspC D B) : ℂ :=
  if h : EmbCond A B ι then (petCOf D petF (petRC D) B : ℂ) * intC B fun x => star (φ.1 (embC h x)) * F.1.1 x else 0

theorem top_int (G : FormGaps D) (hI : TopInt D) {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (h : EmbCond A B ι) (φ : afC D A)
    (F : cuspC D B) : IntegrableOn (fun x => star (φ.1 (embC h x)) * F.1.1 x) (pairC B).2 (pairC B).1 :=
  hI A B ι h.1 _ (embC_spec h) _ _ (pairC_spec G.volEx B).1 (pairC_spec G.volEx B).2.1 _ _ ((mem_afC G.add).1 φ.2)
    ((mem_afC G.add).1 F.1.2) ((mem_cuspC G.add G.cuspInt).1 F.2)

theorem btopC_right (G : FormGaps D) (hI : TopInt D) (petF : HSp D → ℝ) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V)
    (φ : afC D A) : IsLinearMap ℂ (btopC petF A B ι φ) := by
  unfold btopC intC
  by_cases h : EmbCond A B ι
  · simp only [dif_pos h]
    refine ⟨fun F F' => ?_, fun c F => ?_⟩
    · rw [← mul_add, ← integral_add (top_int G hI h φ F) (top_int G hI h φ F')]
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
    · rw [smul_eq_mul, mul_left_comm, ← integral_const_mul c]
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm c]
  · simp only [dif_neg h]
    exact ⟨fun _ _ => by simp, fun _ _ => by simp⟩

theorem btopC_add (G : FormGaps D) (hI : TopInt D) (petF : HSp D → ℝ) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V)
    (φ φ' : afC D A) (F : cuspC D B) : btopC petF A B ι (φ + φ') F = btopC petF A B ι φ F + btopC petF A B ι φ' F := by
  unfold btopC intC
  by_cases h : EmbCond A B ι
  · simp only [dif_pos h]
    rw [← mul_add, ← integral_add (top_int G hI h φ F) (top_int G hI h φ' F)]
    simp only [Submodule.coe_add, Pi.add_apply, star_add, add_mul]
  · simp only [dif_neg h, add_zero]

theorem pairing_smul_left₂ (petF : HSp D → ℝ) (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V)
    (c : ℂ) (φ : afC D A) (F : cuspC D B) : btopC petF A B ι (c • φ) F = star c * btopC petF A B ι φ F := by
  unfold btopC intC
  by_cases h : EmbCond A B ι
  · simp only [dif_pos h]
    rw [mul_left_comm, ← integral_const_mul (star c)]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
  · simp only [dif_neg h, mul_zero]

theorem btopC_eq (G : FormGaps D) (hU : EmbU D) (hR : EmbRat D) (petF : HSp D → ℝ) (A B : HSp D)
    (ι : B.V →ₗ[D.host.E] A.V) (hB : B.SigOK) (hι : HSpace.IsIsomEmb B A ι) (μ : Measure (GA D B)) (𝓕 : Set (GA D B))
    (hp : IsVolPair D B μ 𝓕) (s : GA D B → GA D A) (hs : ∀ h, EmbRel A B ι (s h) h) (φ : afC D A) (F : cuspC D B) :
    btopC petF A B ι φ F = (petCOf D petF (petRC D) B : ℂ) * ∫ h in 𝓕, star (φ.1 (s h)) * F.1.1 h ∂μ := by
  have h : EmbCond A B ι := ⟨hι, s, hs⟩
  have e : s = embC h := funext fun x => hU A B ι hι _ _ _ (hs x) (embC_spec h x)
  unfold btopC
  rw [dif_pos h, e, intC_eq G.volEx G.volU hB hp]
  intro γ hγ x
  obtain ⟨γ', a, -, b⟩ := embC_left hU hR h hγ
  rw [b, ((mem_afC G.add).1 φ.2).left γ' a, ((mem_afC G.add).1 F.1.2).left γ hγ]

section Bessel

variable (ψ : AddChar (AF D.host.F) ℂ) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι)

def NPair (p : Measure (NFlag B d.e) × Set (NFlag B d.e)) : Prop :=
  p.1.IsHaarMeasure ∧ IsFundamentalDomain (NFlagQ B d.e) p.2 p.1 ∧ p.1 p.2 = 1

def besIn (p : Measure (NFlag B d.e) × Set (NFlag B d.e)) (F : GA D B → ℂ) (x : GA D B) : ℂ :=
  ∫ n in p.2, F ((n : GA D B) * x) * star (besChar ψ d (n : GA D B)) ∂p.1

end Bessel

def BesInt1 (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  ∀ p, NPair d p → ∀ F : GA D B → ℂ, IsAutFun B F → ∀ x,
    IntegrableOn (fun n : NFlag B d.e => F ((n : GA D B) * x) * star (besChar ψ d (n : GA D B))) p.2 p.1

def BesInv (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  ∀ p p', NPair d p → NPair d p' → ∀ F : GA D B → ℂ, IsAutFun B F →
    ∀ γ' ∈ GQ B, ∀ γ : GA D A, EmbRel B A ι γ' γ → ∀ x, besIn ψ d p F (γ' * x) = besIn ψ d p' F x

def BesInt2 (ψ : AddChar (AF D.host.F) ℂ) : Prop := ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesDat A B ι),
  HSpace.IsIsomEmb A B ι → ∀ p, NPair d p → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) →
  ∀ (μ : Measure (GA D A)) (𝓕 : Set (GA D A)), μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ →
  ∀ (φ : GA D A → ℂ) (F : GA D B → ℂ), IsAutFunSm (th0 D) A φ → IsCuspFun A φ → IsAutFunSm (th0 D) B F → IsCuspFun B F →
    IntegrableOn (fun h => star (φ h) * besIn ψ d p F (s h * (d.y : GA D B))) 𝓕 μ

theorem proj_ex (A : HSp D) : ∃ g : afC D A →ₗ[ℂ] cuspC D A, g ∘ₗ (cuspC D A).subtype = LinearMap.id :=
  LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)

def projC (A : HSp D) : afC D A →ₗ[ℂ] cuspC D A := (proj_ex A).choose

theorem projC_eq (A : HSp D) (φ : afC D A) (h : φ ∈ cuspC D A) : (projC A φ).1 = φ := by
  have := LinearMap.congr_fun (proj_ex A).choose_spec ⟨φ, h⟩
  exact congrArg Subtype.val this

structure PerGaps (ψ : AddChar (AF D.host.F) ℂ) : Prop where
  embU : EmbU D
  embRat : EmbRat D
  topInt : TopInt D
  int1 : BesInt1 ψ
  inv : BesInv ψ
  int2 : BesInt2 ψ

section Bessel2

variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

open Classical in

def besC (ψ : AddChar (AF D.host.F) ℂ) (petF : HSp D → ℝ) (d : BesDat A B ι) (φ : afC D A) (F : cuspC D B) : ℂ :=
  if h : EmbCond B A ι ∧ ∃ p, NPair d p then
    (petCOf D petF (petRC D) A : ℂ) *
      intC A fun x => star ((projC A φ).1.1 x) * besIn ψ d h.2.choose F.1.1 (embC h.1 x * (d.y : GA D B))
  else 0

theorem bes_int (G : FormGaps D) (P : PerGaps ψ) (d : BesDat A B ι) (h : EmbCond B A ι ∧ ∃ p, NPair d p) (φ : afC D A)
    (F : cuspC D B) : IntegrableOn
      (fun x => star ((projC A φ).1.1 x) * besIn ψ d h.2.choose F.1.1 (embC h.1 x * (d.y : GA D B))) (pairC A).2 (pairC A).1 :=
  P.int2 A B ι d h.1.1 _ h.2.choose_spec _ (embC_spec h.1) _ _ (pairC_spec G.volEx A).1 (pairC_spec G.volEx A).2.1 _ _
    ((mem_afC G.add).1 (projC A φ).1.2) ((mem_cuspC G.add G.cuspInt).1 (projC A φ).2)
    ((mem_afC G.add).1 F.1.2) ((mem_cuspC G.add G.cuspInt).1 F.2)

theorem besC_right (G : FormGaps D) (P : PerGaps ψ) (petF : HSp D → ℝ) (d : BesDat A B ι) (φ : afC D A) :
    IsLinearMap ℂ (besC ψ petF d φ) := by
  unfold besC intC
  by_cases h : EmbCond B A ι ∧ ∃ p, NPair d p
  · simp only [dif_pos h]
    refine ⟨fun F F' => ?_, fun c F => ?_⟩
    · rw [← mul_add, ← integral_add (bes_int G P d h φ F) (bes_int G P d h φ F')]
      congr 2
      funext x
      rw [← mul_add]
      congr 1
      unfold besIn
      rw [← integral_add (P.int1 A B ι d _ h.2.choose_spec _ ((mem_afC G.add).1 F.1.2).toIsAutFun _)
        (P.int1 A B ι d _ h.2.choose_spec _ ((mem_afC G.add).1 F'.1.2).toIsAutFun _)]
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    · rw [smul_eq_mul, mul_left_comm, ← integral_const_mul c]
      congr 2
      funext x
      unfold besIn
      rw [mul_left_comm c, ← integral_const_mul c]
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · simp only [dif_neg h]
    exact ⟨fun _ _ => by simp, fun _ _ => by simp⟩

theorem besC_add (G : FormGaps D) (P : PerGaps ψ) (petF : HSp D → ℝ) (d : BesDat A B ι) (φ φ' : afC D A) (F : cuspC D B) :
    besC ψ petF d (φ + φ') F = besC ψ petF d φ F + besC ψ petF d φ' F := by
  unfold besC intC
  by_cases h : EmbCond B A ι ∧ ∃ p, NPair d p
  · simp only [dif_pos h]
    rw [← mul_add, ← integral_add (bes_int G P d h φ F) (bes_int G P d h φ' F)]
    simp only [map_add, Submodule.coe_add, Pi.add_apply, star_add, add_mul]
  · simp only [dif_neg h, add_zero]

theorem besC_smul (petF : HSp D → ℝ) (d : BesDat A B ι) (c : ℂ) (φ : afC D A) (F : cuspC D B) :
    besC ψ petF d (c • φ) F = star c * besC ψ petF d φ F := by
  unfold besC intC
  by_cases h : EmbCond B A ι ∧ ∃ p, NPair d p
  · simp only [dif_pos h]
    rw [mul_left_comm, ← integral_const_mul (star c)]
    simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
  · simp only [dif_neg h, mul_zero]

theorem embRel_one (A B : HSp D) (ι : B.V →ₗ[D.host.E] A.V) : EmbRel A B ι 1 1 := by
  refine ⟨?_, fun x _ => ?_⟩
  · rw [map_one, map_one, Units.val_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  · rw [map_one, Units.val_one, Matrix.one_mulVec]

theorem besC_eq (G : FormGaps D) (P : PerGaps ψ) (petF : HSp D → ℝ) (d : BesDat A B ι) (hA : A.SigOK)
    (hι : HSpace.IsIsomEmb A B ι) (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (hp : IsVolPair D A μ 𝓕)
    (p : Measure (NFlag B d.e) × Set (NFlag B d.e)) (hN : NPair d p) (s : GA D A → GA D B)
    (hs : ∀ h, EmbRel B A ι (s h) h) (φ : afC D A) (F : cuspC D B) (hφ : IsAniso A ∨ φ ∈ cuspC D A) :
    besC ψ petF d φ F = (petCOf D petF (petRC D) A : ℂ) *
      ∫ h in 𝓕, ∫ n in p.2, star (φ.1 h) * F.1.1 ((n : GA D B) * s h * (d.y : GA D B)) *
        star (besChar ψ d (n : GA D B)) ∂p.1 ∂μ := by
  have h : EmbCond B A ι ∧ ∃ p, NPair d p := ⟨⟨hι, s, hs⟩, p, hN⟩
  have e : s = embC h.1 := funext fun x => P.embU B A ι hι _ _ _ (hs x) (embC_spec h.1 x)
  have hc : φ ∈ cuspC D A := hφ.elim (fun a => Submodule.subset_span fun r C hC => absurd hC (a r C)) id
  have hF := ((mem_afC G.add).1 F.1.2).toIsAutFun
  unfold besC
  rw [dif_pos h, projC_eq A φ hc, intC_eq G.volEx G.volU hA hp]
  · congr 2
    funext x
    have e1 := P.inv A B ι d _ p h.2.choose_spec hN _ hF 1 (one_mem _) 1 (embRel_one B A ι) (embC h.1 x * (d.y : GA D B))
    rw [one_mul] at e1
    rw [e1, e]
    unfold besIn
    rw [← integral_const_mul]
    simp only [mul_assoc]
  · intro γ hγ x
    obtain ⟨γ', a, a', b⟩ := embC_left P.embU P.embRat h.1 hγ
    rw [b, ((mem_afC G.add).1 φ.2).left γ hγ, mul_assoc γ',
      P.inv A B ι d _ _ h.2.choose_spec h.2.choose_spec _ hF γ' a γ a']

end Bessel2

end Formalism.L2.Fam.ThC

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.Inhab

variable {D : D7}

structure ChrIn (D : D7) where
  chr : D.what₂.Tup → ℕ → chrA D
  chr_exp : ∀ μ (j : Fin D.R.m) τ, HasInfExp D (chr μ (j.1 + 1)).1 τ (-(D.hc τ).e j)
  chr_res : ∀ μ j, 1 ≤ j → j ≤ D.R.m → ResEta D (chr μ j).1 0
  eta : chrA D
  eta_exp : ∀ τ, HasInfExp D eta.1 τ (1 / 2)
  eta_res : ResEta D eta.1 1
  eta_unr : UnramEverywhere D eta.1

abbrev lowY (D : D7) (t j i : ℕ) : HSp D := lowC ((towC D t).Ys j) i

structure Free {ψ : AddChar (AF D.host.F) ℂ} (_Om : WeilC ψ) : Type 1 where
  petF : HSp D → ℝ
  petF_pos : ∀ V, 0 < petF V
  fact : ∀ V W, Set (schC ψ V W)
  conjS : ∀ V W, schC ψ V W → schC ψ V W
  conjS_add : ∀ V W Φ Φ', conjS V W (Φ + Φ') = conjS V W Φ + conjS V W Φ'
  conjS_smul : ∀ V W (c : ℂ) Φ, conjS V W (c • Φ) = star c • conjS V W Φ
  conjS_conjS : ∀ V W Φ, conjS V W (conjS V W Φ) = Φ
  conjS_fact : ∀ V W, ∀ Φ ∈ fact V W, conjS V W Φ ∈ fact V W
  conjS_kfin : ∀ V W, ∀ Φ ∈ kfinC ψ V W, conjS V W Φ ∈ kfinC ψ V W

  PosE : ∀ (A B : HSp D), (A.V →ₗ[D.host.E] B.V) → Type
  FJd : ∀ (A B : HSp D), (A.V →ₗ[D.host.E] B.V) → Type
  [fjAdd : ∀ A B ι, AddCommGroup (FJd A B ι)]
  [fjMod : ∀ A B ι, Module ℂ (FJd A B ι)]
  BE : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), PosE A B ι → FJd A B ι → afC D A → cuspC D B → ℂ
  BE_right : ∀ A B ι p s φ, IsLinearMap ℂ (BE A B ι p s φ)
  BE_add : ∀ A B ι p s φ φ' F, BE A B ι p s (φ + φ') F = BE A B ι p s φ F + BE A B ι p s φ' F
  BE_smul : ∀ A B ι p s (c : ℂ) φ F, BE A B ι p s (c • φ) F = star c * BE A B ι p s φ F
  pos1 : D.what₂.Word → {d : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) // (d.y : GA D (D.sp.Y 0)) = 1}
  posSym : D.what₂.Word → {d : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) // (d.y : GA D (D.sp.Y 0)) = 1}

  f1 : ∀ u, Matrix (Fin (D.sp.Y 0).rank) (Fin (pos1 u).1.ρ) D.host.E
  free_flag_dual : ∀ u, IsDualFlag (pos1 u).1 (f1 u)
  colAF : ∀ (u : D.what₂.Word) (_μ : D.what₂.Tup) (j : ℕ), D.what₂.Mu u →ₗ[ℂ] cuspC D (D.sp.X j)
  PhiX : ∀ (_u : D.what₂.Word) (_μ : D.what₂.Tup) (j : ℕ), schC ψ (D.sp.X j) (D.sp.X (j + 1))
  rowAF : ∀ (μ : D.what₂.Tup) (j : ℕ), D.what₂.Mult μ j →ₗ[ℂ] cuspC D (D.sp.Y j)
  PhiY : ∀ (_μ : D.what₂.Tup) (j : ℕ), schC ψ (D.sp.Y (j + 1)) (D.sp.Y j)
  PhiYLow : ∀ (_μ : D.what₂.Tup) (j i : ℕ), schC ψ (D.sp.Y (j + 1)) (lowY D D.R.t j i)
  PhiYupLow : ∀ (_μ : D.what₂.Tup) (j i : ℕ), schC ψ (D.sp.Y j) (lowY D D.R.t (j + 1) i)
  mY : D.what₂.Tup → ℕ → ℝ
  mY_pos : ∀ μ j, 0 < mY μ j
  adelicDataRowMeasureScale_trivialTuple : ∀ j, mY D.what₂.mu0 j = 1
  mY_zero : ∀ μ, mY μ 0 = 1

attribute [instance] Free.fjAdd Free.fjMod

variable {ψ : AddChar (AF D.host.F) ℂ}

def PosC {Om : WeilC ψ} (f : Free Om) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Type :=
  {d : BesDat A B ι // (d.y : GA D B) = 1} ⊕ {_p : f.PosE A B ι // ¬ Odd (B.rank - A.rank)}

def bperC {Om : WeilC ψ} (f : Free Om) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) :
    PosC f A B ι → f.FJd A B ι → afC D A → cuspC D B → ℂ
  | Sum.inl d => fun _ => besC ψ f.petF d.1
  | Sum.inr p => f.BE A B ι p.1

def datC {Om : WeilC ψ} (f : Free Om) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (h : Odd (B.rank - A.rank)) :
    PosC f A B ι → BesDat A B ι
  | Sum.inl d => d.1
  | Sum.inr p => absurd h p.2

def thetaOf (D : D7) {ψ : AddChar (AF D.host.F) ℂ} (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ) (c : ChrIn D)
    (f : Free Om) : ThetaX D where
  AF := fun V => afC D V
  cusp := cuspC D
  pet := petC f.petF
  pet_add_left := fun V F F' H => by
    unfold petC intC
    rw [← mul_add, ← integral_add (pet_int G.volEx G.add G.cuspInt G.petInt V F H)
      (pet_int G.volEx G.add G.cuspInt G.petInt V F' H)]
    simp only [Submodule.coe_add, Pi.add_apply, star_add, add_mul]
  pet_smul_left := fun V a F H => by
    unfold petC intC
    rw [mul_left_comm, ← integral_const_mul (star a)]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
  pet_right := fun V F => ⟨fun H H' => by
      unfold petC intC
      rw [← mul_add, ← integral_add (pet_int G.volEx G.add G.cuspInt G.petInt V F H)
        (pet_int G.volEx G.add G.cuspInt G.petInt V F H')]
      simp only [Submodule.coe_add, Pi.add_apply, mul_add], fun a H => by
      unfold petC intC
      rw [smul_eq_mul, mul_left_comm, ← integral_const_mul a]
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm a]⟩
  pet_symm := fun V F H => by
    unfold petC intC
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← integral_conj]
    simp only [map_mul, Complex.conj_conj, mul_comm]
  pet_pos := petC_pos G.volEx G.add G.cuspInt G.petInt f.petF f.petF_pos
  actR := actRC G.right
  actR_one := fun V τ => by
    ext F x
    unfold actRC
    rw [actC_apply, atTau_one G.atTau, mul_one]
    rfl
  actR_mul := fun V τ g hg h hh => by
    ext F x
    unfold actRC
    rw [Module.End.mul_apply, actC_apply, actC_apply, actC_apply, atTau_mul G.atTau V τ hg hh, mul_assoc]
  actR_cusp := fun V τ g _ => actC_cusp G.right V _ _
  Gf := fun V => GfC V
  actF := actFC G.right
  actF_cusp := fun V g => actC_cusp G.right V _ (Or.inl g.2)
  actF_actR := fun V g τ h => by
    ext F x
    show F.1 (x * (g : GA D V) * atTau (th0 D) V τ h) = F.1 (x * atTau (th0 D) V τ h * (g : GA D V))
    rw [mul_assoc, mul_assoc, fin_inf_comm g.2 (atTau_mem _ V τ h)]
  Ksph := ksphC
  Ksph_mono := fun V S S' hS g hg => ⟨hg.1, hg.2.1, fun v hv => hg.2.2 v (hS hv)⟩
  typ := typC D
  Chr := chrA D
  infTy := infTyC
  infTy_mul := fun χ χ' τ => hE _ τ _ _ (infTyC_spec (χ * χ') τ) (hasInfExp_mul (infTyC_spec χ τ) (infTyC_spec χ' τ))
  chrOf := c.chr
  chrOf_inf := fun μ j τ => hE _ τ _ _ (infTyC_spec _ τ) (c.chr_exp μ j τ)
  etaT := c.eta
  etaT_inf := fun τ => Or.inl (hE _ τ _ _ (infTyC_spec _ τ) (c.eta_exp τ))
  etaT_pos := fun τ => hE _ τ _ _ (infTyC_spec _ τ) (c.eta_exp τ)
  Sch := fun V W => schC ψ V W
  fact := f.fact
  kfin := kfinC ψ
  th := thC G Om f.petF
  Xs := fun t => (towC D t).Xs
  Xs_rank := fun t => (towC D t).Xs_rank
  Xs_sig := fun t => (towC D t).Xs_sig
  Ys := fun t => (towC D t).Ys
  Ys_rank := fun t => (towC D t).Ys_rank
  Ys_sig := fun t => (towC D t).Ys_sig
  iXYs := fun t => (towC D t).iXYs
  iXYs_isom := fun t => (towC D t).iXYs_isom
  iYXm := fun t => (towC D t).iYXm
  iYXm_isom := fun t => (towC D t).iYXm_isom
  YsLow := lowY D
  YsLow_zero := fun _ _ => if_pos rfl
  Xs_rec := fun j _ => by rw [towC_rec]; rfl
  Ys_rec := fun j _ => by rw [towC_rec]; rfl
  conjAF := conjC G.conj
  conjAF_add := conjC_add G.conj
  conjAF_smul := conjC_smul G.conj
  conjAF_conjAF := fun _ _ => Subtype.ext (star_star _)
  conjAF_cusp := conjC_cusp G.conj
  Pos := PosC f
  FJd := f.FJd
  Bper := bperC f
  Bper_right := fun A B ι p s φ => by
    rcases p with d | p
    · exact besC_right G P f.petF d.1 φ
    · exact f.BE_right A B ι p.1 s φ
  Bper_add_left := fun A B ι p s φ φ' F => by
    rcases p with d | p
    · exact besC_add G P f.petF d.1 φ φ' F
    · exact f.BE_add A B ι p.1 s φ φ' F
  Bper_smul_left := fun A B ι p s a φ F => by
    rcases p with d | p
    · exact besC_smul f.petF d.1 a φ F
    · exact f.BE_smul A B ι p.1 s a φ F
  Bper_odd := fun A B ι p h s s' φ F => by
    rcases p with d | p
    · rfl
    · exact absurd h p.2
  Btop := btopC f.petF
  Btop_right := btopC_right G P.topInt f.petF
  Btop_add_left := btopC_add G P.topInt f.petF
  Btop_smul_left := pairing_smul_left₂ f.petF
  pos1 := fun u => Sum.inl (f.pos1 u)
  posSym := fun u => Sum.inl (f.posSym u)
  colAF := f.colAF
  rowAF := f.rowAF
  PhiY := f.PhiY
  PhiYup := fun μ j => swapC ψ _ _ (f.PhiY μ j)
  mY := f.mY
  mY_pos := f.mY_pos
  adelicDataRowMeasureScale_trivialTuple := f.adelicDataRowMeasureScale_trivialTuple
  mY_zero := f.mY_zero

section Ties

variable (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ) (c : ChrIn D) (f : Free Om)

def thetaCompatibilityOf (hS : SpSig D) (hW : WittLow D) : ThetaTied D (thetaOf D G P hE Om c f) where
  ev := fun V => (afC D V).subtype
  ev_inj := fun V => (afC D V).injective_subtype
  ev_aut := fun V F => ((mem_afC G.add).1 F.2).toIsAutFun
  cusp := fun V F => mem_cuspC G.add G.cuspInt
  eGf := fun V => MulEquiv.refl _
  actF := fun _ _ _ _ => rfl
  actR := allSome_fam.2 fun V τ g hg => ⟨(G.atTau V τ g hg).exists, fun h hh F x => by
    rw [← atTau_eq G.atTau hg hh]; rfl⟩
  ksph := fun _ _ _ => Iff.rfl
  conj := fun _ _ _ => rfl
  petF := f.petF
  petF_pos := f.petF_pos
  petR := petRC D
  petR_pos := petRC_pos
  petR_def := fun N => ⟨if_pos (Or.inr rfl), if_pos (Or.inl rfl)⟩
  petR_minf := petRC_minf
  pet := fun V hV μ 𝓕 hp F H => by
    show petC f.petF V F H = _
    unfold petC
    rw [intC_eq G.volEx G.volU hV hp]
    · rfl
    · intro γ hγ x
      rw [((mem_afC G.add).1 F.2).left γ hγ, ((mem_afC G.add).1 H.1.2).left γ hγ]
  btop := fun A B ι hB hι μ 𝓕 hp s hs φ F => btopC_eq G P.embU P.embRat f.petF A B ι hB hι μ 𝓕 hp s hs φ F
  eChr := (chrA D).subtype
  eChr_inj := (chrA D).subtype_injective
  eChr_range := Subtype.range_coe
  infTy := infTyC_spec
  chrOf_res := c.chr_res
  etaT_res := c.eta_res
  etaT_unr := c.eta_unr
  etaT_exp := fun τ => hE _ τ _ _ (infTyC_spec _ τ) (c.eta_exp τ)
  xs_pos := fun t j hj => (towC_sig hS t j hj).1
  ys_sig := fun t j hj => (towC_sig hS t j hj).2
  ysLow := fun t j i h => lowC_spec hW _ (towC_ok t j) i h

def weilCompatibilityOf (hS : SpSig D) (hW : WittLow D) (hψ : IsStdChar D ψ (-1)) :
    WeilTied D (thetaOf D G P hE Om c f) (thetaCompatibilityOf G P hE Om c f hS hW) where
  ψ := ψ
  ψ_std := hψ
  evS := fun V W => (schC ψ V W).subtype
  evS_inj := fun V W => (schC ψ V W).injective_subtype
  evS_range := fun V W _ => Subtype.range_coe
  om := Om.om
  om_heis := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).Heisenberg₂
  om_aut := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).aut
  om_cont := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).cont
  om_unit := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).unit
  om_split := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).split
  om_tw := ⟨fun V W χ χ' ν h => Om.twW_up V W χ χ' ν h.le, fun V W χ χ' ν h => Om.twV_up V W χ χ' ν h.le, Om.twW_dn, Om.twV_dn⟩
  om_swap := fun V W χ χ' a b d => Om.swap V W χ χ' a ⟨b, d⟩
  th := fun V W χ χ' _ b d hV μ 𝓕 hp Φ F h => thC_apply G Om f.petF ⟨b, d⟩ hV hp Φ F h


theorem besselUnipotentSubgroup_zero_subsingleton {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat A B ι) (f0 : Matrix (Fin B.rank) (Fin d.ρ) D.host.E) :
    Subsingleton (besselUnipotentSubgroup d f0 0) := by
  have h : besselUnipotentSubgroup d f0 0 = ⊥ := by
    unfold besselUnipotentSubgroup
    rw [Subgroup.closure_eq_bot_iff]
    rintro g ⟨hg, -⟩
    apply Subtype.ext
    apply Units.ext
    ext i j
    have := hg i j
    rw [RingHom.map_zero, add_zero, zero_mul] at this
    have e : (mt B g - 1) i j = 0 := this.symm
    rw [Matrix.sub_apply, sub_eq_zero] at e
    exact e
  rw [h]
  infer_instance

theorem dirac_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (_ : Subsingleton G) :
    (Measure.dirac (1 : G)).IsHaarMeasure :=
  { toIsMulLeftInvariant := ⟨fun g => by rw [@Subsingleton.elim _ ‹Subsingleton G› g 1]; simp [Measure.map_id']⟩
    toIsFiniteMeasureOnCompacts := inferInstance
    toIsOpenPosMeasure := ⟨fun U _ hne => by
      obtain ⟨x, hx⟩ := hne
      rw [@Subsingleton.elim _ ‹Subsingleton G› x 1] at hx
      rw [Measure.dirac_apply_of_mem hx]
      exact one_ne_zero⟩ }

theorem integral_dirac_one_of_subsingleton {G : Type} [Group G] [MeasurableSpace G] (hs : Subsingleton G) (g : G → ℂ) :
    ∫ x, g x ∂(Measure.dirac (1 : G)) = g 1 := by
  rw [show g = fun _ => g 1 from funext fun x => by rw [@Subsingleton.elim _ hs x 1], integral_const]
  simp

def besselOf (hS : SpSig D) (hW : WittLow D) (hψ : IsStdChar D ψ (-1)) :
    BesselTied D (thetaOf D G P hE Om c f) (thetaCompatibilityOf G P hE Om c f hS hW) (weilCompatibilityOf G P hE Om c f hS hW hψ) where
  dat := datC f
  dat_y := fun A B ι h p => by
    rcases p with d | p
    · exact d.2
    · exact absurd h p.2
  besC := fun _ _ _ _ => 1
  besC_pos := fun _ _ _ _ => one_pos
  bper := fun A B ι ho _ hA hι p hn sF μ 𝓕 hp μN 𝓕N n1 n2 n3 s hs φ F hφ => by
    rcases p with d | p
    · rw [one_mul]
      exact besC_eq G P f.petF d.1 hA hι μ 𝓕 hp (μN, 𝓕N) ⟨n1, n2, n3⟩ s hs φ F hφ
    · exact absurd ho p.2
  besC_one := fun _ _ _ _ => rfl

def b1Of (hS : SpSig D) (hW : WittLow D) (hψ : IsStdChar D ψ (-1)) :
    BesselCompatibility' D (thetaOf D G P hE Om c f) (thetaCompatibilityOf G P hE Om c f hS hW) (weilCompatibilityOf G P hE Om c f hS hW hψ)
      (besselOf G P hE Om c f hS hW hψ) where
  eS := fun _ => 0
  eS_split := fun _ => ⟨∅, fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩
  f := fun u _ => f.f1 u
  f_dual := fun u _ => f.free_flag_dual u
  mu1 := fun u _ => Measure.dirac 1
  mu_one_isHaarMeasure := fun u _ => dirac_haar (besselUnipotentSubgroup_zero_subsingleton (f.pos1 u).1 (f.f1 u))
  bper1 := fun u ho hr hA hι sF μ 𝓕 hp μN 𝓕N n1 n2 n3 s hs φ F hφ => by
    have e := besC_eq G P f.petF (f.pos1 u).1 hA hι μ 𝓕 hp (μN, 𝓕N) ⟨n1, n2, n3⟩ s hs φ F hφ
    refine e.trans (Eq.symm ((integral_dirac_one_of_subsingleton (besselUnipotentSubgroup_zero_subsingleton _ _) _).trans ?_))
    have hb : ∀ p, (besselOf G P hE Om c f hS hW hψ).besC (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) p = 1 := fun _ => rfl
    simp only [OneMemClass.coe_one, mul_one, hb, one_mul]
    rfl

def allCompatibilitiesOf (hS : SpSig D) (hW : WittLow D) (hψ : IsStdChar D ψ (-1)) (h0 : TypZero D) (hA : TypAdd D)
    (hJ : FockCxEx D) (hD : PolAdd ψ) (hR : RealTied D) (A : ProvA) (hP : ProvisionCompatibility D A) : AllTied D (thetaOf D G P hE Om c f) A where
  T := thetaCompatibilityOf G P hE Om c f hS hW
  sm := allSome_fam.2 fun V _ => by
    ext φ
    exact ⟨fun ⟨F, hF⟩ => hF ▸ (mem_afC G.add).1 F.2, fun h => ⟨⟨φ, (mem_afC G.add).2 h⟩, rfl⟩⟩
  ty := allSome_fam.2 fun V hV Q hQ _ F => mem_typC h0 hA hV hQ
  W := weilCompatibilityOf G P hE Om c f hS hW hψ
  unr := fun V W χ χ' _ b d => (Om.weil V W χ χ' ⟨b, d⟩).unr
  kf :=
    { cpt := cptC
      cpt_gram := cptC_gram
      bas := basC
      bas_unit := fun V _ => basC_unit V
      bas_orth := fun V _ => basC_orth V
      cpt_bas := cptC_bas
      kfin := allSome_fam.2 fun V W a b d Φ => mem_kfinC hJ hD a b d Φ }
  phiUp := fun μ j hj x => swapC_apply ψ _ _ (rank_Y_ne (thetaOf D G P hE Om c f) j hj) (f.PhiY μ j) x
  B := besselOf G P hE Om c f hS hW hψ
  real := hR
  prov := hP


end Ties

end Formalism.L2.Fam.ThC

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Host Formalism.L2.JoinChr Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

variable {D : D7}

def plE (τ : D.what₂.Tau) : InfinitePlace D.host.E := InfinitePlace.mk (tauE D τ)

open Classical in

def embAt (τ : D.what₂.Tau) : (plE τ).Completion →+* ℂ :=
  if (plE τ).embedding = tauE D τ then InfinitePlace.Completion.extensionEmbedding (plE τ)
  else (starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding (plE τ))

theorem embAt_alg (τ : D.what₂.Tau) (k : D.host.E) : embAt τ (algebraMap D.host.E (plE τ).Completion k) = tauE D τ k := by
  unfold embAt
  have e1 : InfinitePlace.Completion.extensionEmbedding (plE τ) (algebraMap D.host.E (plE τ).Completion k) =
      (plE τ).embedding k := by simp
  split_ifs with h
  · rw [e1, h]
  · rcases InfinitePlace.embedding_mk_eq (tauE D τ) with h' | h'
    · exact absurd h' h
    · have e2 : (plE τ).embedding = ComplexEmbedding.conjugate (tauE D τ) := h'
      rw [RingHom.comp_apply, e1, e2, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

theorem embAt_cont (τ : D.what₂.Tau) : Continuous (embAt τ) := by
  unfold embAt
  split_ifs
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous
  · exact Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous

theorem conj_tauE_ne (τ τ' : D.what₂.Tau) : ComplexEmbedding.conjugate (tauE D τ) ≠ tauE D τ' := by
  intro h
  have e := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, tauE_sqrtMinusD, tauE_sqrtMinusD] at e
  have e2 := congrArg Complex.im e
  simp at e2
  have := sqrt_d_pos D
  linarith

theorem plE_bij (D : D7) : Function.Bijective (plE (D := D)) := by
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with e | e
    · exact tauE_inj e
    · exact absurd e (conj_tauE_ne τ τ')
  · intro w
    obtain ⟨τ, h | h⟩ := tauE_or w.embedding
    · exact ⟨τ, by unfold plE; rw [h, InfinitePlace.mk_embedding]⟩
    · exact ⟨τ, by unfold plE; rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]⟩

theorem plE_complex (τ : D.what₂.Tau) : (plE τ).IsComplex := by
  rw [plE, InfinitePlace.isComplex_mk_iff]
  exact fun h => conj_tauE_ne τ τ h

structure AdBC (D : D7) where
  Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E
  cont : Continuous Φ
  cont' : Continuous Φ.symm
  inc : ∀ k : D.host.E, Φ (incA D k) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) k

  fin : ∀ x, finPart D x = 1 ↔ (Φ x).2 = 1

  inf : ∀ τ x, embAt τ ((Φ x).1 (plE τ)) = cmpAt D τ x

  idem : ∀ P e, IsPlIdem D e P ↔ Φ e = pairA D.host.E 0 (singleV D.host.E P 1)

  int : ∀ x, finPart D x ∈ intAE D ↔ ∀ P, (Φ x).2 P ∈ P.adicCompletionIntegers D.host.E

  idemF : ∀ v, (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).1 = 0 ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), (P.under (𝓞 D.host.F) = v →
      (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).2 P = 1) ∧
      (P.under (𝓞 D.host.F) ≠ v → (Φ (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)))).2 P = 0)

namespace AdBC

variable (B : AdBC D)

def up : (AE D)ˣ →* Ideles D.host.E := Units.map B.Φ.toMonoidHom

def dn : Ideles D.host.E →* (AE D)ˣ := Units.map B.Φ.symm.toMonoidHom

theorem dn_up (x : (AE D)ˣ) : B.dn (B.up x) = x := Units.ext (by simp [up, dn])

theorem up_dn (x : Ideles D.host.E) : B.up (B.dn x) = x := Units.ext (by simp [up, dn])

theorem up_inc (k : D.host.Eˣ) : B.up (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k := Units.ext (by simp [up, B.inc]; rfl)

theorem toUnits_cont : Continuous Circle.toUnits := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  exact continuous_subtype_val.comp (continuous_inv : Continuous fun z : Circle => z⁻¹)

def toH : chrA D →* HChar D.host.E where
  toFun χ := ⟨(Circle.toUnits.comp χ.1).comp B.dn,
    (toUnits_cont.comp χ.2.1.1).comp (Continuous.units_map _ B.cont'), fun k => by
      rw [← B.up_inc, MonoidHom.comp_apply, B.dn_up, MonoidHom.comp_apply, χ.2.1.2, map_one]⟩
  map_one' := Subtype.ext (MonoidHom.ext fun _ => map_one Circle.toUnits)
  map_mul' _ _ := Subtype.ext (MonoidHom.ext fun _ => map_mul Circle.toUnits _ _)

theorem toH_up (χ : chrA D) (x : (AE D)ˣ) : (((B.toH χ).1 (B.up x) : ℂˣ) : ℂ) = (χ.1 x : ℂ) := by
  show ((Circle.toUnits (χ.1 (B.dn (B.up x))) : ℂˣ) : ℂ) = _
  rw [B.dn_up]
  rfl

theorem toH_inj : Function.Injective B.toH := by
  intro χ χ' h
  apply Subtype.ext
  ext x
  have := congrArg (fun ψ : HChar D.host.E => ((ψ.1 (B.up x) : ℂˣ) : ℂ)) h
  simpa only [toH_up] using this

theorem toH_unitary (χ : chrA D) : (B.toH χ).IsUnitary := by
  intro x
  show ‖((Circle.toUnits (χ.1 (B.dn x)) : ℂˣ) : ℂ)‖ = 1
  exact Circle.norm_coe _

theorem up_inf (τ : D.what₂.Tau) (u : (plE τ).Completionˣ) (x : (AE D)ˣ) (h1 : finPart D (x : AE D) = 1)
    (h2 : ∀ τ', τ' ≠ τ → cmpAt D τ' (x : AE D) = 1) (h3 : cmpAt D τ (x : AE D) = embAt τ u) :
    B.up x = infIdele D.host.E (plE τ) u := by
  apply Units.ext
  refine Prod.ext (funext fun w => ?_) ((B.fin x).1 h1)
  obtain ⟨τ', rfl⟩ := (plE_bij D).2 w
  apply (embAt τ').injective
  refine (B.inf τ' x).trans ?_
  by_cases e : τ' = τ
  · subst e
    rw [h3]
    exact congrArg _ (infIdele_fst_self D.host.E _ u).symm
  · rw [h2 τ' e, ← (embAt τ').map_one]
    exact congrArg _ (infIdele_fst_ne D.host.E _ _ (fun a => e ((plE_bij D).1 a)) u).symm

theorem toH_inf (χ : chrA D) (a : D.what₂.Tau → ℚ) (h : ∀ τ, HasInfExp D χ.1 τ (a τ)) : (B.toH χ).HasInfQ (embTau D) a := by
  classical
  choose n hn he using h
  refine ⟨n, hn, fun k => ?_⟩
  have e1 : (B.toH χ).inf k = ∏ w : InfinitePlace D.host.E, (B.toH χ).1 (infIdele D.host.E w (atInf w k)) := by
    show (B.toH χ).1 (infDiag k) = _
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, map_prod]
    rfl
  rw [e1, Units.coe_prod, ← Fintype.prod_bijective _ (plE_bij D) _ _ (fun _ => rfl)]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hk : tauE D τ k ≠ 0 := (map_ne_zero _).2 k.ne_zero
  let x := mkU (D := D) (fun τ' => if τ' = τ then tauE D τ k else 1) (fun τ' => by split_ifs; exacts [hk, one_ne_zero])
  have h1 : finPart D (x : AE D) = 1 := finPart_mkAE _ _
  have h2 : ∀ τ', τ' ≠ τ → cmpAt D τ' (x : AE D) = 1 := fun τ' h => (cmpAt_mkAE _ _ τ').trans (if_neg h)
  have h3 : cmpAt D τ (x : AE D) = tauE D τ k := (cmpAt_mkAE _ _ τ).trans (if_pos rfl)
  rw [← B.up_inf τ _ x h1 h2 (h3.trans (embAt_alg τ k).symm), B.toH_up, allSome_fam.1 (he τ) x h1 h2]
  have h3' : th0 D τ (infPart D (x : AE D)) = tauE D τ k := h3
  rw [h3']
  rfl

end AdBC

section Dens

variable {L : Type} [Field L] [NumberField L]

def inl1 : ((w : InfinitePlace L) → w.Completion) →* AdeleRing (𝓞 L) L where
  toFun y := ((y : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (mul_one 1).symm

theorem infinite_inclusion_continuous : Continuous (inl1 (L := L)) := continuous_id.prodMk continuous_const

theorem infinite_inclusion_single (w : InfinitePlace L) (u : w.Completionˣ) :
    Units.map inl1 (Units.map (by classical exact MonoidHom.mulSingle (fun w : InfinitePlace L => w.Completion) w) u) =
      infIdele L w u := rfl

theorem infinite_inclusion_diagonal (k : Lˣ) :
    Units.map inl1 (Units.map (algebraMap L ((w : InfinitePlace L) → w.Completion)).toMonoidHom k) = infDiag k := by
  classical
  unfold infDiag
  rw [MonoidHom.finsetProd_apply]
  simp only [MonoidHom.comp_apply, ← infinite_inclusion_single, ← map_prod]
  congr 1
  apply Units.ext
  rw [Units.coe_prod]
  exact (Finset.univ_prod_mulSingle _).symm

theorem dense_units : DenseRange (Units.map (algebraMap L ((w : InfinitePlace L) → w.Completion)).toMonoidHom) := by
  have h : Dense (Set.range (algebraMap L ((w : InfinitePlace L) → w.Completion))) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap L
  have : Nontrivial ((w : InfinitePlace L) → w.Completion) := inferInstanceAs (Nontrivial (InfiniteAdeleRing L))
  refine (h.preimage Units.isOpenEmbedding_val.isOpenMap).mono ?_
  rintro u ⟨k, hk⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact u.ne_zero hk.symm
  exact ⟨Units.mk0 k h0, Units.ext hk⟩

theorem fin_inf (hc : ∀ w : InfinitePlace L, w.IsComplex) (χ : HChar L) (h : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) (k : Lˣ) :
    χ.inf k = 1 := by
  obtain ⟨n, hn, hχ⟩ := h
  show χ.1 (infDiag k) = 1
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (hc w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (atInf w k : w.Completion)) hn
  have hz' : e.symm z ^ n = (atInf w k : w.Completion) := by rw [← map_pow, hz, e.symm_apply_apply]
  have h0 : e.symm z ≠ 0 := fun a => (atInf w k).ne_zero (by rw [← hz', a, zero_pow hn.ne'])
  have e2 : atInf w k = Units.mk0 _ h0 ^ n := Units.ext hz'.symm
  rw [MonoidHom.comp_apply, e2, map_pow, map_pow]
  exact DFunLike.congr_fun (congrArg Subtype.val hχ) _

end Dens

namespace AdBC

variable (B : AdBC D)

def secOfH0 (χ : HChar D.host.E) (hu : χ.IsUnitary) : (AE D)ˣ →* Circle where
  toFun x := ⟨χ.1 (B.up x), mem_sphere_zero_iff_norm.2 (hu _)⟩
  map_one' := Circle.ext (by show ((χ.1 (B.up 1) : ℂˣ) : ℂ) = 1; rw [map_one, map_one]; rfl)
  map_mul' x y := Circle.ext (by
    show ((χ.1 (B.up (x * y)) : ℂˣ) : ℂ) = (χ.1 (B.up x) : ℂ) * (χ.1 (B.up y) : ℂ)
    rw [map_mul, map_mul, Units.val_mul])

theorem unitary_hecke_infinity_type (χ : HChar D.host.E) (hu : χ.IsUnitary) (a : D.what₂.Tau → ℚ) (h : χ.HasInfQ (embTau D) a) (τ : D.what₂.Tau) :
    HasInfExp D (B.secOfH0 χ hu) τ (a τ) := by
  classical
  obtain ⟨n, hn, he⟩ := h
  refine ⟨n τ, hn τ, allSome_fam.2 fun x h1 h2 => ?_⟩
  have hne : ∀ (y : ((w : InfinitePlace D.host.E) → w.Completion)ˣ) τ', embAt τ' (y.1 (plE τ')) ≠ 0 := fun y τ' =>
    ((y.isUnit.map (Pi.evalRingHom (fun w : InfinitePlace D.host.E => w.Completion) (plE τ'))).map (embAt τ')).ne_zero
  have hc : ∀ τ', Continuous fun y : ((w : InfinitePlace D.host.E) → w.Completion)ˣ => embAt τ' (y.1 (plE τ')) :=
    fun τ' => (embAt_cont τ').comp ((continuous_apply _).comp Units.continuous_val)
  have key : ∀ y : ((w : InfinitePlace D.host.E) → w.Completion)ˣ, ((χ.1 (Units.map inl1 y) : ℂˣ) : ℂ) =
      ∏ τ', (embAt τ' (y.1 (plE τ')) / ((‖embAt τ' (y.1 (plE τ'))‖ : ℝ) : ℂ)) ^ n τ' := by
    intro y
    refine dense_units.induction_on y (isClosed_eq ?_ ?_) fun k => ?_
    · exact Units.continuous_val.comp (χ.2.1.comp (Continuous.units_map _ infinite_inclusion_continuous))
    · refine continuous_finsetProd _ fun τ' _ => Continuous.zpow₀ ((hc τ').div
        (Complex.continuous_ofReal.comp (hc τ').norm) fun y => ?_) _ fun y => Or.inl ?_
      · exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne y τ'))
      · exact div_ne_zero (hne y τ') (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne y τ')))
    · rw [infinite_inclusion_diagonal]
      refine (he k).trans (Finset.prod_congr rfl fun τ' _ => ?_)
      have : embAt τ' ((Units.map (algebraMap D.host.E ((w : InfinitePlace D.host.E) → w.Completion)).toMonoidHom k).1
        (plE τ')) = embTau D τ' k := embAt_alg τ' k
      rw [this]
  let y : ((w : InfinitePlace D.host.E) → w.Completion)ˣ :=
    Units.map (RingHom.fst (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)).toMonoidHom (B.up x)
  have ey : Units.map inl1 y = B.up x := Units.ext (Prod.ext rfl ((B.fin x).1 h1).symm)
  have ec : ∀ τ', embAt τ' (y.1 (plE τ')) = th0 D τ' (infPart D (x : AE D)) := fun τ' => B.inf τ' x
  show ((χ.1 (B.up x) : ℂˣ) : ℂ) = _
  rw [← ey, key, Finset.prod_eq_single τ, ec]
  · intro τ' _ h
    rw [ec, h2 τ' h]
    simp
  · intro h
    exact absurd (Finset.mem_univ τ) h

def ofH (χ : HChar D.host.E) (hu : χ.IsUnitary) (a : D.what₂.Tau → ℚ) (h : χ.HasInfQ (embTau D) a) : chrA D :=
  ⟨B.secOfH0 χ hu, ⟨Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp (Continuous.units_map _ B.cont))) _,
    fun k => Circle.ext (by
      show ((χ.1 (B.up _) : ℂˣ) : ℂ) = 1
      rw [B.up_inc, χ.2.2]; rfl)⟩, fun τ => ⟨_, B.unitary_hecke_infinity_type χ hu a h τ⟩⟩

theorem toH_ofH (χ : HChar D.host.E) (hu : χ.IsUnitary) (a : D.what₂.Tau → ℚ) (h : χ.HasInfQ (embTau D) a) :
    B.toH (B.ofH χ hu a h) = χ := by
  apply Subtype.ext
  ext x
  show ((χ.1 (B.up (B.dn x)) : ℂˣ) : ℂ) = ((χ.1 x : ℂˣ) : ℂ)
  rw [B.up_dn]

def ResTriv : Prop := ∀ χ : HChar D.host.E, χ.TrivOn D.host.F → ∀ a, χ.1 (B.up (idF D a)) = 1

def EtaIs : Prop := ∀ χ : chrA D, (B.toH χ).ResEta D.host.F → IsEta D (χ.1.comp (idF D))

def UnrAll : Prop := ∀ χ : chrA D, (∀ v, (B.toH χ).UnrAt v) → UnramEverywhere D χ.1

end AdBC

def EtaU (D : D7) : Prop := ∀ η η', IsEta D η → IsEta D η' → η = η'

structure ChrGaps (B : AdBC D) : Prop where
  triv : B.ResTriv
  etaIs : B.EtaIs
  unr : B.UnrAll
  etaU : EtaU D

theorem hasInf_tau (χ : HChar D.host.E) (n : D.R.Psi → ℤ) (h : χ.HasInf (embPsi D.host) n) :
    χ.HasInf (embTau D) (fun τ => n (D.eTau τ)) := by
  intro k
  rw [h k]
  exact (Fintype.prod_equiv D.eTau
    (fun τ => (embPsi D.host (D.eTau τ) (k : D.host.E) / ((‖embPsi D.host (D.eTau τ) (k : D.host.E)‖ : ℝ) : ℂ)) ^ n (D.eTau τ))
    (fun g => (embPsi D.host g (k : D.host.E) / ((‖embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g) (fun _ => rfl)).symm

theorem eta_inf (C : CharFrame D) : C.eta.HasInfQ (embTau D) (fun _ => 1 / 2) :=
  ⟨fun _ => 1, fun _ => by norm_num, hasInf_tau C.eta _ C.isEta.inf⟩

section Frame

variable {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch)

theorem tup_unitary (μ : D.what₂.Tup) (j : Fin D.R.m) : (Tp.tup μ j).IsUnitary := by
  obtain ⟨n, hn, h⟩ := Tp.xi_fin μ
  exact (C.isMu0 j).unitary.mul (HChar.isUnitary_of_order hn h)

theorem tup_inf (μ : D.what₂.Tup) (j : Fin D.R.m) : (Tp.tup μ j).HasInfQ (embTau D) (fun τ => -(D.hc τ).e j) := by
  obtain ⟨n, hn, hinf⟩ := (C.isMu0 j).inf
  refine ⟨fun τ => n (D.eTau τ), fun τ => by rw [hn]; simp [eExp], fun k => ?_⟩
  have h0 := fin_inf (fun w => by obtain ⟨τ, rfl⟩ := (plE_bij D).2 w; exact plE_complex τ) (Tp.xi μ) (Tp.xi_fin μ) k
  show (((C.mu0 j).inf k * (Tp.xi μ).inf k : ℂˣ) : ℂ) = _
  rw [h0, mul_one]
  exact hasInf_tau _ n hinf k

variable (B : AdBC D)

def chrTup (μ : D.what₂.Tup) (j : ℕ) : chrA D :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then B.ofH _ (tup_unitary Tp μ ⟨j - 1, by omega⟩) _ (tup_inf Tp μ _) else 1

theorem chrTup_succ (μ : D.what₂.Tup) (j : Fin D.R.m) :
    chrTup Tp B μ (j.1 + 1) = B.ofH _ (tup_unitary Tp μ j) _ (tup_inf Tp μ j) := by
  have h : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ D.R.m := ⟨by omega, j.2⟩
  simp [chrTup, h]

def chrInOf (G : ChrGaps B) : ChrIn D :=
  have he : IsEta D ((B.ofH C.eta C.isEta.unitary _ (eta_inf C)).1.comp (idF D)) :=
    G.etaIs _ (by rw [B.toH_ofH]; exact C.isEta.res)
  { chr := chrTup Tp B
    chr_exp := fun μ j τ => by rw [chrTup_succ]; exact B.unitary_hecke_infinity_type _ (tup_unitary Tp μ j) _ (tup_inf Tp μ j) τ
    chr_res := fun μ j h1 h2 => by
      unfold chrTup
      rw [dif_pos ⟨h1, h2⟩]
      refine ⟨⟨_, he⟩, fun η _ a => Circle.ext ?_⟩
      rw [pow_zero]
      exact congrArg Units.val (G.triv _ ((C.isMu0 _).triv.mul (Tp.xi_triv μ)) a)
    eta := B.ofH C.eta C.isEta.unitary _ (eta_inf C)
    eta_exp := B.unitary_hecke_infinity_type _ C.isEta.unitary _ (eta_inf C)
    eta_res := ⟨⟨_, he⟩, fun η hη a => by rw [pow_one, G.etaU η _ hη he]; rfl⟩
    eta_unr := G.unr _ (by rw [B.toH_ofH]; exact C.isEta.unr) }

variable {ψ : AddChar (AF D.host.F) ℂ} (Gc : ChrGaps B) (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ)
  (f : Free Om)

def thetaChrOf : ThetaChrTied D C nch Tp (thetaOf D G P hE Om (chrInOf Tp B Gc) f) where
  eChr := B.toH
  inj := B.toH_inj
  range := fun χ => ⟨fun ⟨c, hc⟩ => hc ▸ ⟨B.toH_unitary c, _, B.toH_inf c _ (infTyC_spec c)⟩,
    fun ⟨hu, a, ha⟩ => ⟨B.ofH χ hu a ha, B.toH_ofH χ hu a ha⟩⟩
  infTy := fun c => B.toH_inf c _ (infTyC_spec c)
  chrOf := fun μ j => by
    show B.toH (chrTup Tp B μ (j.1 + 1)) = _
    rw [chrTup_succ, B.toH_ofH]
  etaT := B.toH_ofH _ C.isEta.unitary _ (eta_inf C)


end Frame

end Formalism.L2.Fam.ThC

end
end
