import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFramesCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundX
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WittExtensionTheorem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FibreOrbits.FibreOrbitOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FixedPointsGramVector

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

section
variable {k r : ℕ}

def Rel (z z' : Fin (2 * r + k + 1) → ℂ) (a b : B.Mat k r) : Prop :=
  ∃ n ∈ C2.N0set k r z, ∃ m ∈ C2.N0set k r z, ∃ n' ∈ C2.N0set k r z', ∃ m' ∈ C2.N0set k r z',
  ∃ c ∈ UWset k r z, ∃ c' ∈ UWset k r z',
    b = c * (n⁻¹ * a * n') * c' ∧ c * (m⁻¹ * a * m') * c' = a

def nrm (T : B.Mat k r → B.Mat k r × B.Mat k r) (g : B.Mat k r) : B.Mat k r := (T g).1 * g * (T g).2

end

def GramSlice : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
  ∃ T : B.Mat k r → B.Mat k r × B.Mat k r,
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → (T g).1 ∈ UWset k r z ∧ (T g).2 ∈ UWset k r z') ∧
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, T (n⁻¹ * g * n') = T g) ∧
    (∀ g₁ ∈ B.GV k r, ∀ g₂ ∈ B.GV k r, 0 < Gf k r z z' g₁ → Zhat k r z z' g₁ = Zhat k r z z' g₂ →
      Rel z z' (nrm T g₁) (nrm T g₂)) ∧
    (∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ → ∃ (O : Set (B.Mat k r)) (Tl : B.Mat k r → B.Mat k r × B.Mat k r),
      IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Tl O ∧
      ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
        (Tl g).1 ∈ UWset k r z ∧ (Tl g).2 ∈ UWset k r z' ∧ Rel z z' (nrm Tl g) (nrm T g))

def SmoothRep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq),
    (∀ h₀ ∈ UWset k r D.z, ∃ (O : Set (B.Mat k r)) (P : B.Mat k r → (Wp →L[ℂ] Wp)),
      IsOpen O ∧ h₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P O ∧ ∀ h ∈ O, h ∈ UWset k r D.z → P h = D.π h) ∧
    (∀ h₀ ∈ UWset k r D.z', ∃ (O : Set (B.Mat k r)) (P : B.Mat k r → (Wq →L[ℂ] Wq)),
      IsOpen O ∧ h₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P O ∧ ∀ h ∈ O, h ∈ UWset k r D.z' → P h = D.π' h)

def FibEquivU : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ0 μ0' : Measure (Mt k r)), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), ∀ c ∈ UWset k r D.z, ∀ c' ∈ UWset k r D.z',
      fibInt D μ0 μ0' F (c * g * c') = (D.π c).comp ((fibInt D μ0 μ0' F g).comp (D.π' c'))

def FiberIntegralUnipotentInvariant : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ0 μ0' : Measure (Mt k r)), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), ∀ n ∈ C2.N0set k r D.z, ∀ n' ∈ C2.N0set k r D.z',
      fibInt D μ0 μ0' F (n⁻¹ * g * n') = fibInt D μ0 μ0' F g

section
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

def repE (A : W →L[ℂ] W) : W ≃L[ℂ] W := by
  classical
  exact if hA : ∀ v, ‖A v‖ = ‖v‖ then
    (LinearEquiv.ofInjectiveEndo (A : W →ₗ[ℂ] W) (fun v w h => by
      have h1 := hA (v - w)
      have h2 : A (v - w) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr h
      rw [h2, norm_zero] at h1
      exact sub_eq_zero.mp (norm_eq_zero.mp h1.symm))).toContinuousLinearEquiv
  else ContinuousLinearEquiv.refl ℂ W


end

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]


theorem one_mem_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  simp [UWset, UH]



end


end PI.UnitaryGroupMassFormula.DLm.Gram
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6 Formalism.QuantumDeterminants.BesselUnitaryEquiv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

end PI.UnitaryGroupMassFormula.DLm.Gram
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

theorem unipotent_normal_unitary {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {a u : B.Mat k r}
    (ha : a ∈ UWset k r z) (hu : u ∈ C2.N0set k r z) : a * u * a⁻¹ ∈ C2.N0set k r z := by
  have hN := (unitary_weyl_normal_holds k r z hz.1 a ha u hu.1).1
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have h1N : (1 : B.Mat k r) ∈ Nset k r := ((PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz).one_mem).1
  have hS_a : a ∈ Sset k r z := ⟨a, ha, 1, h1N, (mul_one a).symm⟩
  have hS_u : u ∈ Sset k r z := ⟨1, one_mem_UW z, u, hu.1, (one_mul u).symm⟩
  have hS_c : a * u * a⁻¹ ∈ Sset k r z := ⟨1, one_mem_UW z, _, hN, (one_mul _).symm⟩
  have hua : IsUnit a.det := WeylGroupFacts.isUnit_of_uh ha.1
  have e : a * u * a⁻¹ * a = a * u := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hua, Matrix.mul_one]
  have h2 := (hF.1 _ hS_c).2.2 a hS_a
  have h3 := (hF.1 a hS_a).2.2 u hS_u
  refine ⟨hN, ?_⟩
  rw [e, h3, hF.2 a ha, hu.2] at h2
  simpa using h2.symm

end PI.UnitaryGroupMassFormula.DLm.Gram
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

def GsWitt : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ g₁ ∈ B.GV k r, ∀ g₂ ∈ B.GV k r, 0 < Gf k r z z' g₁ → Zhat k r z z' g₁ = Zhat k r z z' g₂ →
      ∃ c ∈ UWset k r z, ∃ n ∈ C2.N0set k r z, ∃ n' ∈ C2.N0set k r z', ∃ c' ∈ UWset k r z',
        g₂ = c * (n⁻¹ * g₁ * n') * c'

def GsFrames : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
  ∃ Fr : B.Mat k r → Set (B.Mat k r × B.Mat k r),
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → (Fr g).Nonempty) ∧
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ p ∈ Fr g, p.1 ∈ UWset k r z ∧ p.2 ∈ UWset k r z') ∧
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, Fr (n⁻¹ * g * n') = Fr g) ∧
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ c ∈ UWset k r z, ∀ n ∈ C2.N0set k r z, ∀ n' ∈ C2.N0set k r z',
      ∀ c' ∈ UWset k r z', ∀ p ∈ Fr g, (p.1 * c⁻¹, c'⁻¹ * p.2) ∈ Fr (c * (n⁻¹ * g * n') * c')) ∧
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ p ∈ Fr g, ∀ q ∈ Fr g, Rel z z' (p.1 * g * p.2) (q.1 * g * q.2)) ∧
    (∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ → ∃ (O : Set (B.Mat k r)) (Fl : B.Mat k r → B.Mat k r × B.Mat k r),
      IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fl O ∧
      ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g → Fl g ∈ Fr g)

section rel

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}

theorem rel_of (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {a b x y : B.Mat k r} (hx : x ∈ C2.N0set k r z)
    (hy : y ∈ C2.N0set k r z') (hb : b = x * a * y) : Rel z z' a b := by
  have Gz := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz
  have Gz' := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz'
  have hux := Gz.unit x hx
  refine ⟨x⁻¹, Gz.inv_mem x hx, 1, Gz.one_mem, y, hy, 1, Gz'.one_mem, 1, one_mem_UW z, 1, one_mem_UW z', ?_, ?_⟩
  · rw [Matrix.nonsing_inv_nonsing_inv x hux, hb]; simp
  · simp

theorem mem_of_rel (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {a b : B.Mat k r} (h : Rel z z' a b) :
    ∃ x ∈ C2.N0set k r z, ∃ y ∈ C2.N0set k r z', b = x * a * y := by
  obtain ⟨n, hn, m, hm, n', hn', m', hm', c, hc, c', hc', hb, ha⟩ := h
  have Gz := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz
  have Gz' := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz'
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have hcu := Wz.unit c hc
  have hcu' := Wz'.unit c' hc'
  have hmu := Gz.unit m hm
  have hmu' := Gz'.unit m' hm'
  have K : m * c⁻¹ * a * c'⁻¹ * m'⁻¹ = a := by
    calc m * c⁻¹ * a * c'⁻¹ * m'⁻¹ = m * c⁻¹ * (c * (m⁻¹ * a * m') * c') * c'⁻¹ * m'⁻¹ := by rw [ha]
      _ = a := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.mul_nonsing_inv_cancel_left c' _ hcu', Matrix.mul_nonsing_inv m' hmu', Matrix.mul_one,
          Matrix.nonsing_inv_mul_cancel_left c _ hcu, Matrix.mul_nonsing_inv_cancel_left m _ hmu]
  have hP : c * n⁻¹ * c⁻¹ ∈ C2.N0set k r z := unipotent_normal_unitary hz hc (Gz.inv_mem n hn)
  have hX : c * m * c⁻¹ ∈ C2.N0set k r z := unipotent_normal_unitary hz hc hm
  have hY : c'⁻¹ * m'⁻¹ * c' ∈ C2.N0set k r z' := by
    have := unipotent_normal_unitary hz' (Wz'.inv_mem c' hc') (Gz'.inv_mem m' hm')
    rwa [Matrix.nonsing_inv_nonsing_inv c' hcu'] at this
  have hQ : c'⁻¹ * n' * c' ∈ C2.N0set k r z' := by
    have := unipotent_normal_unitary hz' (Wz'.inv_mem c' hc') hn'
    rwa [Matrix.nonsing_inv_nonsing_inv c' hcu'] at this
  refine ⟨c * n⁻¹ * c⁻¹ * (c * m * c⁻¹), Gz.mul_mem _ hP _ hX, c'⁻¹ * m'⁻¹ * c' * (c'⁻¹ * n' * c'),
    Gz'.mul_mem _ hY _ hQ, ?_⟩
  calc b = c * (n⁻¹ * a * n') * c' := hb
    _ = c * (n⁻¹ * (m * c⁻¹ * a * c'⁻¹ * m'⁻¹) * n') * c' := by rw [K]
    _ = c * n⁻¹ * c⁻¹ * (c * m * c⁻¹) * a * (c'⁻¹ * m'⁻¹ * c' * (c'⁻¹ * n' * c')) := by
        simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hcu,
          Matrix.mul_nonsing_inv_cancel_left _ _ hcu']

theorem rel_trans (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {a b c : B.Mat k r} (h1 : Rel z z' a b)
    (h2 : Rel z z' b c) : Rel z z' a c := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_of_rel hz hz' h1
  obtain ⟨x', hx', y', hy', rfl⟩ := mem_of_rel hz hz' h2
  refine rel_of hz hz' ((PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz).mul_mem _ hx' _ hx)
    ((PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz').mul_mem _ hy _ hy') ?_
  simp only [Matrix.mul_assoc]

end rel

theorem gf_eq_of_zhat {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g₁ g₂ : B.Mat k r}
    (h : Zhat k r z z' g₁ = Zhat k r z z' g₂) : Gf k r z z' g₂ = Gf k r z z' g₁ := by
  unfold Gf Dmin
  rw [h]

open Classical in
theorem gramSlice_of (hW : GsWitt) (hF : GsFrames) : GramSlice := by
  intro k r z z' hk hr hz hz'
  obtain ⟨Fr, hne, hU, hinv, heq, hrel, hloc⟩ := hF k r z z' hk hr hz hz'
  let T : B.Mat k r → B.Mat k r × B.Mat k r := fun g => if h : (Fr g).Nonempty then h.some else (1, 1)
  have hT : ∀ g ∈ B.GV k r, 0 < Gf k r z z' g → T g ∈ Fr g := by
    intro g hg hG
    have h := hne g hg hG
    simp only [T, dif_pos h]
    exact h.some_mem
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have Gz := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz
  have Gz' := PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z' hz'
  refine ⟨T, fun g hg hG => hU g hg hG _ (hT g hg hG), ?_, ?_, ?_⟩
  · intro g hg hG n hn n' hn'
    simp only [T, hinv g hg hG n hn n' hn']
  · intro g₁ hg₁ g₂ hg₂ hG₁ hZ
    have hG₂ : 0 < Gf k r z z' g₂ := by rw [gf_eq_of_zhat hZ]; exact hG₁
    obtain ⟨c, hc, n, hn, n', hn', c', hc', e⟩ := hW k r z z' hk hr hz hz' g₁ hg₁ g₂ hg₂ hG₁ hZ
    set p := T g₁ with hp
    have hp1 : p ∈ Fr g₁ := hT g₁ hg₁ hG₁
    obtain ⟨hpa, hpb⟩ := hU g₁ hg₁ hG₁ p hp1
    have hp2 : (p.1 * c⁻¹, c'⁻¹ * p.2) ∈ Fr g₂ := by
      rw [e]; exact heq g₁ hg₁ hG₁ c hc n hn n' hn' c' hc' p hp1
    have hr1 : Rel z z' (nrm T g₁) (p.1 * c⁻¹ * g₂ * (c'⁻¹ * p.2)) := by
      have hua := Wz.unit p.1 hpa
      have hub := Wz'.unit p.2 hpb
      have hcu := Wz.unit c hc
      have hcu' := Wz'.unit c' hc'
      have hx : p.1 * n⁻¹ * p.1⁻¹ ∈ C2.N0set k r z := unipotent_normal_unitary hz hpa (Gz.inv_mem n hn)
      have hy : p.2⁻¹ * n' * p.2 ∈ C2.N0set k r z' := by
        have := unipotent_normal_unitary hz' (Wz'.inv_mem p.2 hpb) hn'
        rwa [Matrix.nonsing_inv_nonsing_inv p.2 hub] at this
      refine rel_of hz hz' hx hy ?_
      show p.1 * c⁻¹ * g₂ * (c'⁻¹ * p.2) = p.1 * n⁻¹ * p.1⁻¹ * (p.1 * g₁ * p.2) * (p.2⁻¹ * n' * p.2)
      rw [e]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hcu, Matrix.nonsing_inv_mul_cancel_left _ _ hua,
        Matrix.mul_nonsing_inv_cancel_left _ _ hcu', Matrix.mul_nonsing_inv_cancel_left _ _ hub]
    have hr2 : Rel z z' (p.1 * c⁻¹ * g₂ * (c'⁻¹ * p.2)) (nrm T g₂) :=
      hrel g₂ hg₂ hG₂ _ hp2 _ (hT g₂ hg₂ hG₂)
    exact rel_trans hz hz' hr1 hr2
  · intro g₀ hg₀ hG₀
    obtain ⟨O, Fl, hO, hgO, hs, hFl⟩ := hloc g₀ hg₀ hG₀
    refine ⟨O, Fl, hO, hgO, hs, fun g hgO' hg hG => ?_⟩
    have h1 := hFl g hgO' hg hG
    obtain ⟨ha, hb⟩ := hU g hg hG _ h1
    exact ⟨ha, hb, hrel g hg hG _ h1 _ (hT g hg hG)⟩

end PI.UnitaryGroupMassFormula.DLm.Gram
end
end

section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Lifts

namespace FLW

variable {n : ℕ}

theorem herm_add_l (H : Matrix (Fin n) (Fin n) ℂ) (u u' w : Fin n → ℂ) :
    herm H (u + u') w = herm H u w + herm H u' w := by
  simp [herm, Matrix.mulVec_add, dotProduct_add]

theorem herm_smul_l (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (u w : Fin n → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_add_r (H : Matrix (Fin n) (Fin n) ℂ) (u w w' : Fin n → ℂ) :
    herm H u (w + w') = herm H u w + herm H u w' := by
  simp [herm, star_add, add_dotProduct]

theorem herm_smul_r (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (u w : Fin n → ℂ) :
    herm H u (c • w) = star c * herm H u w := by
  simp [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem unitary_of_herm (H M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ u v, herm H (M *ᵥ u) (M *ᵥ v) = herm H u v) :
    Mᴴ * H * M = H := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  simp only [herm, Matrix.mulVec_single_one] at this
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  convert this using 1
  · simp [dotProduct, Matrix.mulVec, Matrix.col, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    rw [Finset.sum_comm]
  · simp [dotProduct, Matrix.mulVec, Pi.single_apply]

end FLW

theorem wittHpk (k r : ℕ) {ι : Type} [Fintype ι] (x y : ι → Fin (2 * r + k + 1) → ℂ)
    (hx : LinearIndependent ℂ x) (hy : LinearIndependent ℂ y)
    (hg : ∀ i j, herm (Hpk k r) (x i) (x j) = herm (Hpk k r) (y i) (y j)) :
    ∃ g ∈ B.GV k r, ∀ i, g *ᵥ x i = y i := by
  set H := Hpk k r with hHdef
  have hHh : Hᴴ = H := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
  have hHH : H * H = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  let Bf : (Fin (2 * r + k + 1) → ℂ) →ₗ⋆[ℂ] (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun u v => herm H v u)
      (fun u u' v => FLW.herm_add_r H v u u')
      (fun c u v => by rw [FLW.herm_smul_r, smul_eq_mul]; rfl)
      (fun u v v' => FLW.herm_add_l H v v' u)
      (fun c u v => by rw [FLW.herm_smul_l, smul_eq_mul]; rfl)
  have hB : ∀ u v, Bf u v = herm H v u := fun u v => rfl
  have hsym : ∀ a b, star (Bf a b) = Bf b a := by
    intro a b
    rw [hB, hB, ggHerm_swap H hHh a b]
  have hnd : ∀ a, (∀ b, Bf a b = 0) → a = 0 := by
    intro a ha
    have h0 := ha (H *ᵥ a)
    rw [hB] at h0
    simp only [herm, Matrix.mulVec_mulVec, hHH, Matrix.one_mulVec] at h0
    have h1 : ∑ i, Complex.normSq (a i) = 0 := by
      have : (∑ i, Complex.normSq (a i) : ℂ) = star a ⬝ᵥ a := by
        simp [dotProduct, Complex.mul_conj, mul_comm]
      exact_mod_cast this.trans h0
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (a j))).1 h1 i (Finset.mem_univ _)
    simpa using this
  let U := Submodule.span ℂ (Set.range x)
  let bU : Module.Basis ι ℂ U := Module.Basis.span hx
  have hbU : ∀ a, (bU a : Fin (2 * r + k + 1) → ℂ) = x a := fun a => by
    show ((Module.Basis.span hx a : U) : Fin (2 * r + k + 1) → ℂ) = x a
    rw [Module.Basis.span_apply]
  let f : U →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) := bU.constr ℂ y
  have hf : ∀ a, f (bU a) = y a := fun a => bU.constr_basis ℂ y a
  have hfsum : ∀ u : U, f u = ∑ a, bU.repr u a • y a := by
    intro u
    conv_lhs => rw [← bU.sum_repr u]
    rw [map_sum]; simp only [map_smul, hf]
  have husum : ∀ u : U, (u : Fin (2 * r + k + 1) → ℂ) = ∑ a, bU.repr u a • x a := by
    intro u
    conv_lhs => rw [← bU.sum_repr u]
    rw [Submodule.coe_sum]; simp only [Submodule.coe_smul, hbU]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [hfsum] at hu
    have hc := Fintype.linearIndependent_iff.mp hy _ hu
    have : bU.repr u = 0 := by ext a; simp [hc a]
    simpa using this
  have hsum_l : ∀ (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ),
      herm H (∑ a, c a • v a) w = ∑ a, c a * herm H (v a) w := by
    intro c v w
    simp [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  have hsum_r : ∀ (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ),
      herm H w (∑ a, c a • v a) = ∑ a, star (c a) * herm H w (v a) := by
    intro c v w
    simp [herm, star_sum, star_smul, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hisom : ∀ u v : U, Bf (f u) (f v) = Bf u v := by
    intro u v
    rw [hB, hB, hfsum, hfsum, husum, husum, hsum_l, hsum_l]
    apply Finset.sum_congr rfl; intro a _
    rw [hsum_r, hsum_r]
    congr 1
    apply Finset.sum_congr rfl; intro b _
    rw [hg]
  obtain ⟨g, hgB, hgf⟩ := _root_.witt_extension_theorem ℂ (Fin (2 * r + k + 1) → ℂ) Bf hsym hnd U f hinj hisom
  refine ⟨LinearMap.toMatrix' (g : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ)), ?_, fun i => ?_⟩
  · show _ * H * _ = H
    apply FLW.unitary_of_herm
    intro u v
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    have := hgB v u
    rw [hB, hB] at this
    exact this
  · rw [LinearMap.toMatrix'_mulVec]
    have := hgf (bU i)
    rw [hbU, hf] at this
    exact this

end PI.UnitaryGroupMassFormula.DLm.Lifts
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram


theorem parabolic_levi_unipotent_decomp {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {s : B.Mat k r}
    (hs : s ∈ C2.CurvatureSupportSet k r z) : ∃ h ∈ UWset k r z, ∃ m ∈ C2.N0set k r z, s = h * m := by
  obtain ⟨⟨h, hh, m, hm, rfl⟩, hu⟩ := hs
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have h1N : (1 : B.Mat k r) ∈ Nset k r := ((PI.UnitaryGroupMassFormula.DLm.unipotent_integral_closed k r z hz).one_mem).1
  have hS_h : h ∈ Sset k r z := ⟨h, hh, 1, h1N, (mul_one h).symm⟩
  have hS_m : m ∈ Sset k r z := ⟨1, one_mem_UW z, m, hm, (one_mul m).symm⟩
  have e := (hF.1 h hS_h).2.2 m hS_m
  rw [hF.2 h hh, Matrix.one_mul, hu] at e
  exact ⟨h, hh, m, ⟨hm, e.symm⟩, rfl⟩


end PI.UnitaryGroupMassFormula.DLm.Gram
end
end

section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

def GsSliceP : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
  ∃ S : Set (B.Mat k r),
    (∀ y ∈ S, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, n * y * n' ∈ S) ∧
    (∀ y ∈ S, ∀ α ∈ UWset k r z, ∀ β ∈ UWset k r z', α * y * β ∈ S → Rel z z' y (α * y * β)) ∧
    (∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ → ∃ (O : Set (B.Mat k r)) (Fl : B.Mat k r → B.Mat k r × B.Mat k r),
      IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fl O ∧
      ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
        (Fl g).1 ∈ UWset k r z ∧ (Fl g).2 ∈ UWset k r z' ∧ (Fl g).1 * g * (Fl g).2 ∈ S)



end PI.UnitaryGroupMassFormula.DLm.Gram
end
end
