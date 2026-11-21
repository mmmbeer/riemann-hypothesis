import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.ComplexMatrixMajorantIntegrable

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace Ad3.K.LC.C

def WhittakerSchwartzBound : Prop := ∀ k : ℕ, 3 ≤ k → ∀ N : ℕ, ∃ (C : ℝ) (N' : ℕ), ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ)
  (M : Matrix (Fin 2) (Fin 2) ℂ), M.det ≠ 0 →
    ‖W2 k f M‖ ≤ C * pS N' f * Yb M ^ ((1 : ℝ) / 2) * (1 + |Real.log (Yb M)|) / (1 + Yb M) ^ N

def ge (ε : ℝ) (u : ℂ) : ℝ := Real.exp (-Real.pi * ε ^ 2 * ‖u‖ ^ 2)

def Aq (Ψ : Sw) (ε : ℝ) (k : M22) (v : ℂ) (q : Fin 2 → ℂ) : ℂ :=
  ∫ z : Fin 2 → ℂ, Ψ (Matrix.of.symm (Matrix.of k * blk z), q) * psiC (-(z 1)) * (ge ε (z 0 - v) : ℂ)

def Hw (k : ℕ) (n : ℤ) (s : ℂ) (f : (Fin 2 → ℂ) → ℂ) (v : ℂ) (κ : M22) : ℂ :=
  W2 k f (w2 * d2 (-1 / v) * (Matrix.of κ)⁻¹) * ph (-n) v * ((‖v‖ ^ 2 : ℝ) : ℂ) ^ (-1 / 2 - s)

def Dk (N : ℕ) (κ : M22) : ℝ :=
  (max (‖(Matrix.of κ).det‖ ^ 2)
    (‖κ 0 0 * (starRingEnd ℂ) (κ 0 1) + κ 1 0 * (starRingEnd ℂ) (κ 1 1)‖ ^ 2 / (‖κ 0 1‖ ^ 2 + ‖κ 1 1‖ ^ 2)))⁻¹ /
    (1 + ‖κ‖) ^ N

def UnipotentJointIntegrability : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 → ∀ u : ℂ,
  Integrable (fun p : ℂˣ × M22 => chC n s p.1 * ((‖(p.1 : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ *
    (((‖(Matrix.of p.2).det‖⁻¹ : ℝ) : ℂ) * W2 k (innQ Ψ (cyc u) p.2 (p.1 : ℂ)⁻¹) (Matrix.of p.2)⁻¹)) (mulC.prod volume)

def UnipotentTateFunctionalEquation : Prop := ∀ k : ℕ, 3 ≤ k → ∀ (Ψ : Sw) (n : ℤ) (s : ℂ), 0 < s.re → s.re < 1 → ∀ (g : GL (Fin 3) ℂ) (h : M22)
  (M : Matrix (Fin 2) (Fin 2) ℂ), (Matrix.of h).det ≠ 0 → M.det ≠ 0 →
    ∫ t : ℂˣ, chC n s t * ((‖(t : ℂ)‖ ^ 2 : ℝ) : ℂ)⁻¹ * W2 k (innQ Ψ g h (t : ℂ)⁻¹) M ∂mulC =
      (1 / 2 : ℂ) * (-1) ^ n * gC n s * ∫ x : Fin 2 → ℂ, ph n (x 1) * ((‖x 1‖ ^ 2 : ℝ) : ℂ) ^ (s - 1) *
        W2 k (sl Ψ (Matrix.of.symm (Matrix.of h * blk x * (g : Matrix (Fin 3) (Fin 3) ℂ)))) M

def HAbs : Prop := ∀ k : ℕ, 3 ≤ k → ∀ σ : ℝ, 0 < σ → σ < 1 → ∃ (C : ℝ) (N : ℕ), ∀ (f : SchwartzMap (Fin 2 → ℂ) ℂ)
  (n : ℤ) (s : ℂ), s.re = σ → ∀ κ : M22, (Matrix.of κ).det ≠ 0 → Integrable (fun v => Hw k n s f v κ) ∧
    ∫ v, ‖Hw k n s f v κ‖ ≤ C * pS N f * (‖(Matrix.of κ).det‖ ^ 2 / (‖κ 0 1‖ ^ 2 + ‖κ 1 1‖ ^ 2) ^ 2) ^ (σ - 1 / 2)

end Ad3.K.LC.C
