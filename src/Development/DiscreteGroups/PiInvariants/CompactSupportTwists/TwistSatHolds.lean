import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.RgJS

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def locT (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) : Module.End ℂ (Sm E n) :=
  finRep E n (locGL E n w g)

def piZ (π : CuspSub E n) (z : ℂ) : Set (Sm E n) :=
  {f | ∃ ψ ∈ π.V, ∀ g, f.1 g = ψ.1 g * Complex.exp (z * logAbs g.val.det)}

def FixAt (w : HeightOneSpectrum (𝓞 E)) (f : Sm E n) : Prop := ∀ k ∈ GlobalTheory.LFun.KGL w n, locT w k f = f

def InKgK (w : HeightOneSpectrum (𝓞 E)) (g y : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∃ k₁ ∈ GlobalTheory.LFun.KGL w n, ∃ k₂ ∈ GlobalTheory.LFun.KGL w n, y = k₁ * g * k₂

def IsHk (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) (R : Finset (GL (Fin n) (w.adicCompletion E))) :
    Prop :=
  (∀ r ∈ R, InKgK w g r) ∧ ∀ y, InKgK w g y → ∃! r, r ∈ R ∧ r⁻¹ * y ∈ GlobalTheory.LFun.KGL w n

def hk (w : HeightOneSpectrum (𝓞 E)) (R : Finset (GL (Fin n) (w.adicCompletion E))) : Module.End ℂ (Sm E n) :=
  ∑ r ∈ R, locT w r

end Defs

def HeckeFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n) (z : ℂ)
  (U : Submodule ℂ (Sm E n)), IsStable U → (∀ φ ∈ U, IsAutForm φ) → ∀ φ ∈ U,
  ∃ (S : Finset (HeightOneSpectrum (𝓞 E))) (V₀ : Submodule ℂ (Sm E n)), FiniteDimensional ℂ V₀ ∧ V₀ ≤ U ∧ φ ∈ V₀ ∧
    (∀ w, w ∉ S → ∀ f ∈ V₀, FixAt w f) ∧
    (∀ w, w ∉ S → ∀ g R, IsHk w g R → ∀ f ∈ V₀, hk w R f ∈ V₀) ∧
    (∀ w, w ∉ S → ∀ w', w' ∉ S → ∀ g g' R R', IsHk w g R → IsHk w' g' R' →
      ∀ f ∈ V₀, hk w R (hk w' R' f) = hk w' R' (hk w R f)) ∧
    (∀ w, w ∉ S → ∃ v ∈ piZ π z, v ≠ 0 ∧ FixAt w v) ∧
    (∀ w, w ∉ S → ∀ g R, IsHk w g R → ∃ c : ℂ, ∀ v ∈ piZ π z, FixAt w v → hk w R v = c • v)

end DiscreteGroups.T1.G

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.RgJS
open GlobalTheory.LFun Formalism.UG GlobalTheory.PRep

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def sclQ (w : HeightOneSpectrum (𝓞 E)) (u : ℂ) (B : Multiset ℂˣ) : Multiset ℂ :=
  B.map fun b : ℂˣ => (b : ℂ) * ((qV E w : ℕ) : ℂ) ^ u

end Defs

def TwistSat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (m : ℕ) (σ : CuspSub E m) (u : ℂ),
  ∃ σ' : CuspSub E m, ∀ᶠ w in Filter.cofinite, ∀ B : Multiset ℂˣ, (CG.mk σ).HasSat w B →
    ∃ B' : Multiset ℂˣ, (CG.mk σ').HasSat w B' ∧ B'.map (fun b : ℂˣ => (b : ℂ)) = sclQ w u B

end DiscreteGroups.T1.G

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun Formalism.UG GlobalTheory.PRep

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem absC_loc (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℤ)
    (hx : Valued.v (x : w.adicCompletion E) = WithZero.exp (-n)) :
    (((Model.absC E u).loc w x : ℂˣ) : ℂ) = Complex.exp (u * (-(n * Real.log (Ideal.absNorm w.asIdeal : ℕ)) : ℝ)) := by
  change Complex.exp (u * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = _
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w x n hx]

theorem absC_unrAt (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E u).UnrAt w := by
  intro x hx
  apply Units.ext
  rw [absC_loc u w x 0 (by rw [hx]; simp)]
  simp

theorem absC_val (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    (((Model.absC E u).val w : ℂˣ) : ℂ) = ((qV E w : ℕ) : ℂ) ^ (-u) := by
  have hu : Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = WithZero.exp (-(1 : ℤ)) :=
    unif_spec w
  have h := absC_loc u w (atFin w (unif w)) 1 hu
  change (((Model.absC E u).loc w (atFin w (unif w)) : ℂˣ) : ℂ) = _
  rw [h, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 (qV_ne_zero w))]
  have e : Complex.log ((qV E w : ℕ) : ℂ) = ((Real.log (Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast]; rfl
  rw [e]
  congr 1
  push_cast
  ring


end DiscreteGroups.T1.G

end
end
