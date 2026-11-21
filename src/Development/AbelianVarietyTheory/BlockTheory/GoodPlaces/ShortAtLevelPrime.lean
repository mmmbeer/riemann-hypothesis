import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramified

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ShortPlaceDegreesAtLevelPrime

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

variable {D : D7}

def degPlus {j : ℕ} (w : WeightFamilies.Wt D j) : ℕ := ∑ t, ∑ k, w.aP t k

def degMinus {j : ℕ} (w : WeightFamilies.Wt D j) : ℕ := ∑ t, ∑ k, w.aM t k

def frn {j : ℕ} (w : WeightFamilies.Wt D j) : ℕ := D.R.f * D.R.r * w.n

def v_vw {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (x : K) : ℝ := ((vLa la x : ℤ) : ℝ)

def Oriented (T : Full D) (i : Fin 2) (π : 𝓞 D.host.E) : Prop :=
  π * T.Q.H.bar π = (D.host.g i : 𝓞 D.host.E) ∧ T.Q.l.Mb ≤ Ideal.span {T.Q.H.bar π}

def ShortAtLevelPrime : Prop :=
  ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ), InR D j → ∀ (w : WeightFamilies.Wt D j) (g : T.R j), g ∈ T.toTop.sh j w →
    ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la) (i : Fin 2) (π : 𝓞 D.host.E) (τ : D.host.E →+* ℂ),
      ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal → Oriented T i π → InPsi T.Q.H τ →
      ((-((degPlus w : ℝ) * v_vw la (embK T.Q.c τ π) + (degMinus w : ℝ) * v_vw la (embK T.Q.c τ (T.Q.H.bar π)) +
          (frn w : ℝ) * v_vw la ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F)) : ℝ) : EReal) ≤ vAtV y g

theorem Oriented.ne_zero {T : Full D} {i : Fin 2} {π : 𝓞 D.host.E} (h : Oriented T i π) :
    π ≠ 0 ∧ T.Q.H.bar π ≠ 0 := by
  have hg : ((D.host.g i : ℕ) : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.host.g_prime i).ne_zero
  rw [← h.1] at hg
  exact mul_ne_zero_iff.1 hg

end GlobalTheory.IndefiniteRowSideFullHecke.ShortPlaceDegreesAtLevelPrime
