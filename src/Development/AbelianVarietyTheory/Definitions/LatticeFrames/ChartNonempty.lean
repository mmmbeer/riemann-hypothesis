import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.Model
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

section Gen
variable (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

theorem mt_mul (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one : mt V (1 : GA D V) = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem finM_mul (g h : GA D V) : finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  simp only [finM, mt_mul, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_mul

theorem finM_one : finM V hn (1 : GA D V) = 1 := by
  subst hn
  simp only [finM, mt_one, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem infM_eq (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn g τ = ((mt V g).map ((θ τ).comp (infPart D))).reindex (finCongr hn) (finCongr hn) := rfl

theorem infM_mul (g h : GA D V) (τ : D.what₂.Tau) : infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn
  simp only [infM_eq, mt_mul, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_mul

theorem infM_one (τ : D.what₂.Tau) : infM θ V hn (1 : GA D V) τ = 1 := by
  subst hn
  simp only [infM_eq, mt_one, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem infM_unit (g : GA D V) (τ : D.what₂.Tau) : IsUnit (infM θ V hn g τ).det := by
  have h := infM_mul θ V hn g g⁻¹ τ
  rw [mul_inv_cancel, infM_one] at h
  exact Matrix.isUnit_det_of_right_inverse h.symm

def finGL (g : GA D V) : GL (Fin n) (EF D) :=
  ⟨finM V hn g, finM V hn g⁻¹, by rw [← finM_mul, mul_inv_cancel, finM_one], by rw [← finM_mul, inv_mul_cancel, finM_one]⟩

theorem toEAf_conj (a : AE D) :
    toEAf D (cA D a) = Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]


theorem finGL_mem (g : GA D V) :
    finGL V hn g ∈ UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  subst hn
  have hg : cT (cA D) (mt V g) * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2
  have h2 := congrArg (fun M => M.map (toEAf D)) hg
  simp only [Matrix.map_mul] at h2
  change cT _ (finM V rfl g) * _ * finM V rfl g = _
  simp only [finM, finCongr_refl, Matrix.reindex_refl_refl]
  have e1 : cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((mt V g).map (toEAf D)) =
      (cT (cA D) (mt V g)).map (toEAf D) := by
    ext i j; simp only [cT, Matrix.transpose_apply, Matrix.map_apply, toEAf_conj]
  have e2 : V.gram.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) = (V.gram.map (incA D)).map (toEAf D) := rfl
  rw [e1, e2]; exact h2

def trFr {G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (g : GA D V) (y : Frames G) : Frames G :=
  ⟨fun τ => infM θ V hn g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (infM_unit θ V hn g τ).mul (y.2 τ)⟩

variable {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (yc : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))

theorem exists_dec (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S))) (g : GA D V) :
    ∃ p, IsDec S yc (finM V hn g) p := by
  obtain ⟨c, hc⟩ := hy (Quotient.mk'' ⟨finGL V hn g, finGL_mem V hn g⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := (DoubleCoset.eq _ _ (yc c) _).1 hc
  obtain ⟨γ, hγ, e⟩ := Subgroup.mem_subgroupOf.1 ha
  refine ⟨(c, γ, ⟨b.1, Subgroup.mem_subgroupOf.1 hb⟩), hγ, ?_⟩
  have := congrArg (fun x => x.1.1) hab
  simp only at this
  rw [e]; exact this

set_option maxHeartbeats 2000000 in

theorem rdS_res (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC _ (embT D))) (g : GA D V) :
    rdS θ V hn S yc (fun c => Ψ (yc c)) y g = Ψ ⟨finGL V hn g, finGL_mem V hn g⟩ (trFr θ V hn g y) := by
  have h := exists_dec V hn S yc hy g
  rw [rdS, dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  generalize h.choose = p at h1 h2 ⊢
  have hi : ∀ τ, atInf (embT D) p.2.1.1 τ * atInf (embT D) (p.2.1⁻¹ : GL (Fin n) D.host.E).1 τ = 1 := by
    intro τ
    simp only [atInf]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : ∀ τ, IsUnit (atInf (embT D) (p.2.1⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * y.1 τ).det := by
    intro τ
    rw [Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_det_of_left_inverse (hi τ)).mul (infM_unit θ V hn g τ)).mul (y.2 τ)
  rw [atFr, dif_pos hu]
  refine (hΨ p.2.1 h1 (yc p.1) _ p.2.2 (Units.ext h2) _ _ ?_).symm
  intro τ
  simp only [trFr]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hi, Matrix.one_mul]



set_option maxHeartbeats 2000000 in

theorem rdS_right_lev (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC _ (embT D))) (g k : GA D V) (κ : S.U)
    (hk : finM V hn k = κ.1.1) (hk' : ∀ τ, infM θ V hn k τ = 1) :
    rdS θ V hn S yc (fun c => Ψ (yc c)) y (g * k) = (S.chi κ : ℂ) * rdS θ V hn S yc (fun c => Ψ (yc c)) y g := by
  rw [rdS_res θ V hn S yc hy Ψ hΨ, rdS_res θ V hn S yc hy Ψ hΨ]
  refine hΨ 1 (one_mem _) _ _ κ ?_ _ _ ?_
  · apply Units.ext
    change finM V hn (g * k) = _
    rw [finM_mul, hk]
    simp only [map_one, one_mul, Units.val_mul]
    rfl
  · intro τ
    simp only [trFr, infM_mul, hk', atInf, Units.val_one, mul_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]



end Gen

variable {u : D.what₂.Word}


variable {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)




end GlobalTheory.AdForm.Model
