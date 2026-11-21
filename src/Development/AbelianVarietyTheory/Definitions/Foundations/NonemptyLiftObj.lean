import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel

noncomputable section
namespace GlobalTheory.Glob.IntegralWittCoefficients.Model
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem nonempty_place (p : ℕ) [Fact p.Prime] : Nonempty (Qbar →+* ℂ_[p]) :=
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  ⟨(IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[p])).toRingHom⟩

def ofRec {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) : G1 p := ⟨g.lam, g.abelian₂, g.C, g.wq, g.ex⟩


theorem exists_at (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K))
    (h1 : IsCurveIdeal D cc) (h3 : Nat.Coprime (Ideal.absNorm cc) p) :
    ∃ (δ : ℂ) (g : G1 p), At D cc δ g ∧ g.lam = lam := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (TaylorLogMetric.discr (lamOf D cc 1)) (n := 12) (by norm_num)
  obtain ⟨g, hg, hl, -⟩ := GlobalTheory.GenusOneDatum.exists_genusOne_datum D (GlobalTheory.UnitModel.modelEx_holds D) p lam cc δ
    ⟨h1, hδ⟩ h3
  exact ⟨δ, ofRec g, hg, hl⟩


def stdLat (E : Type) [Field E] [NumberField E] (N : ℕ) : Submodule (𝓞 E) (Fin N → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

theorem mem_range_iff {E : Type} [Field E] [NumberField E] (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_stdLat {E : Type} [Field E] [NumberField E] {N : ℕ} (x : Fin N → E) :
    x ∈ stdLat E N ↔ ∀ k, IsIntegral ℤ (x k) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
  exact forall_congr' fun k => mem_range_iff (x k)

theorem isSDLat_std (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) : IsSDLat E N (stdLat E N) := by
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → E) ∈ stdLat E N := fun k => by
    rw [mem_stdLat]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [mem_range_iff]
    rw [mem_stdLat] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd E).toIntAlgHom).mul (hy i)
  · rw [mem_stdLat]
    intro k
    have := h _ (hs k)
    rw [mem_range_iff] at this
    simpa [stdH, Pi.single_apply, apply_ite] using this

def frameChain (D : D7) (u : D.what₂.Word) : ColumnChain D.R D.what₂.Tau (D.hcW u) where
  cls _ := Unit
  clsFin _ := inferInstance
  stab _ _ := Unit
  stabGrp _ _ := inferInstance
  stabFin _ _ := inferInstance
  DGam := 1
  DGam_pos := one_pos
  dvd_DGam _ _ _ := by simp
  Y i := {f : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ // ∀ τ, (f τ).det ≠ 0}
  de _ y τ := (y.1 τ).det
  de_ne _ y τ := y.2 τ
  rhoDet _ _ := 1
  rhoDet' _ _ := 1
  rho_norm _ _ _ := norm_one
  rho'_norm _ _ _ := norm_one
  unf _ _ _ := 0
  sSharp := (D.mem u).C.sSharp
  sSharp_eq := (D.mem u).C.sSharp_eq
  sDiv := (D.mem u).C.sDiv
  sDiv_eq := (D.mem u).C.sDiv_eq


end GlobalTheory.Glob.IntegralWittCoefficients.Model
