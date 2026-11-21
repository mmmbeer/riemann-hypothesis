import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ExpansionTerms

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgBcC.RealD

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC.Real

variable {n : ℕ}

def hwK {W : Type*} [AddCommGroup W] [Module ℂ W] (F : Fin n → Fin n → Module.End ℂ W) (μ : Fin n → ℝ) : Submodule ℂ W where
  carrier := {v | Formalism.REAL.KHighest (fun _ => true) F μ v}
  add_mem' {x y} hx hy := ⟨fun a => by rw [map_add, hx.1 a, hy.1 a, smul_add],
    fun a b hab he => by rw [map_add, hx.2 a b hab he, hy.2 a b hab he, add_zero]⟩
  zero_mem' := ⟨fun a => by simp, fun a b _ _ => by simp⟩
  smul_mem' c x hx := ⟨fun a => by rw [map_smul, hx.1 a, smul_comm], fun a b hab he => by rw [map_smul, hx.2 a b hab he, smul_zero]⟩

def HarmTop : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → harmSet lam ⊆ topTypes lam

end PositivityTheory.RgBcC.RealD
