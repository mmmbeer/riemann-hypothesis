import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.HkEqUOp

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

section LocEigAux

open UpperTheory.V.Hi UpperTheory.V.AlgebraTools

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private noncomputable def mu (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) : kˣ →* ℂˣ :=
  ψ i * (absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2))⁻¹

private noncomputable def omg (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) : kˣ →* ℂˣ := ψ i * absPow k (-(((n : ℂ) - 1) / 2))

private theorem om_unit (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) {y : kˣ} (hy : valuation k (y : k) = 1) : omg ψ i y = ψ i y := by
  simp [omg, isUnram_absPow k _ y hy]

private theorem mu_unit (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) {y : kˣ} (hy : valuation k (y : k) = 1) : mu ψ i y = ψ i y := by
  simp [mu, isUnram_absPow k _ y hy]

private theorem mu_unif (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) :
    (mu ψ i (UpperTheory.V.Hi.unif k) : ℂ) = (omg ψ i (UpperTheory.V.Hi.unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹ := by
  have hq : nabs k (UpperTheory.V.Hi.unif k) = (Nat.card 𝓀[k] : ℝ)⁻¹ := GlobalTheory.GLDoubling.nabs_unif GlAx.unif_spec
  have e : mu ψ i = omg ψ i * absPow k ((i : ℕ) : ℂ) := by
    have hi := i.2
    rw [mu, omg, mul_assoc, ← absPow_add, ← absPow_neg, modExp_fin _ (fun _ => by simp)]
    congr 2
    push_cast
    ring
  rw [e, MonoidHom.mul_apply, Units.val_mul, val_absPow, hq, Complex.cpow_natCast]
  simp

private theorem diagT_inj : Function.Injective (diagT k (Fin n)) := by
  intro s t h
  funext i
  have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i i) h
  simp only [val_diagT, Matrix.diagonal_apply_eq] at this
  exact Units.ext this

private theorem upow_mem {a : Fin n → ℤ} (ha : Antitone a) : upow k n a ∈ (glIwa k n).P := ⟨a, ha, rfl⟩

end LocEigAux
