import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ScalarCharacterTwist

open Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

section Val

variable {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)

def HasVal_vp (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) (r : ℚ) : Prop :=
  ∃ (n : ℕ) (k : K), 0 < n ∧ k ≠ 0 ∧ σ k = z ^ n ∧ (ordE w k : ℚ) = (n : ℚ) * r * (eW w : ℚ)

def UnitAtW (w : HeightOneSpectrum (𝓞 K)) (z : ℂ) : Prop := HasVal_vp σ w z 0

theorem ordE_pow (w : HeightOneSpectrum (𝓞 K)) (k : K) (n : ℕ) : ordE w (k ^ n) = n * ordE w k := by
  unfold ordE
  rw [map_pow, WithZero.log_pow]
  simp

theorem hasVal_vp_iff (w : HeightOneSpectrum (𝓞 K)) (k : K) (r : ℚ) :
    HasVal_vp σ w (σ k) r ↔ k ≠ 0 ∧ (ordE w k : ℚ) = r * (eW w : ℚ) := by
  constructor
  · rintro ⟨n, k', hn, hk', h1, h2⟩
    have h3 : k' = k ^ n := σ.injective (by rw [h1, map_pow])
    subst h3
    refine ⟨fun h => hk' (by rw [h, zero_pow hn.ne']), ?_⟩
    rw [ordE_pow] at h2
    push_cast at h2
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    apply mul_left_cancel₀ hn'
    rw [h2, mul_assoc]
  · rintro ⟨h0, h⟩
    exact ⟨1, k, one_pos, h0, by rw [pow_one], by rw [h]; simp⟩

theorem unitAtW_iff (w : HeightOneSpectrum (𝓞 K)) (k : K) : UnitAtW σ w (σ k) ↔ w.valuation K k = 1 := by
  unfold UnitAtW
  rw [hasVal_vp_iff, zero_mul]
  constructor
  · rintro ⟨h0, h⟩
    have h1 : w.valuation K k ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : WithZero.log (w.valuation K k) = 0 := by
      have : ordE w k = 0 := by exact_mod_cast h
      unfold ordE at this
      omega
    rw [← WithZero.exp_log h1, h2, WithZero.exp_zero]
  · intro h
    refine ⟨fun h0 => by simp [h0] at h, ?_⟩
    unfold ordE
    rw [h]
    simp

end Val

section Cls

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def vpLat (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E 1) where
  carrier := {x | ∀ y ∈ (conjPrime₂ P).asIdeal, ∃ z ∈ P.asIdeal, algebraMap (𝓞 E) E z = algebraMap (𝓞 E) E y * x 0}
  zero_mem' := fun _ _ => ⟨0, P.asIdeal.zero_mem, by simp⟩
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨z, hz, e⟩ := ha y hy
    obtain ⟨z', hz', e'⟩ := hb y hy
    refine ⟨z + z', P.asIdeal.add_mem hz hz', ?_⟩
    rw [map_add, e, e', Pi.add_apply, mul_add]
  smul_mem' := by
    intro c a ha y hy
    obtain ⟨z, hz, e⟩ := ha y hy
    refine ⟨c * z, P.asIdeal.mul_mem_left c hz, ?_⟩
    rw [map_mul, e, Pi.smul_apply, Algebra.smul_def]
    ring

def FrOf {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} (N : Submodule (𝓞 E) (Sp E n)) (fr : Frs E n SB) : Prop :=
  ∀ (P : SB) (x : Sp E n), fr P x ∈ localization₂ P.1.asIdeal N ↔ x ∈ stdAt E n P.1

def StdAt {n : ℕ} (ST : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) : Prop :=
  ∀ P ∈ ST, localization₂ P.asIdeal N = stdAt E n P

end Cls

section Chars

variable {D : Dat} {H : D7} (s : Seam H D.X) (χ : TaylorLogMetric.IdE H → ℂ)
  (sel : HeightOneSpectrum (𝓞 D.X.F) → HeightOneSpectrum (𝓞 D.X.E)) {S : Set ℕ}
  (mu : Tup D.X.F D.X.E D.X.K S) (cst : LocCst D.X (rowSG D.Pr sel mu))

def chiDet {n : ℕ} (N : Submodule (𝓞 D.X.E) (Sp D.X.E n)) : ℂ := χ (TaylorLogMetric.detId H (StandardLatticesGL3.stdL H n) (s.lat N))

def sExp (D : Dat) (i : Fin D.R.m) (τ : D.X.Tau) : ℚ := (D.W.row τ).e i - (D.R.N i.1 : ℚ) / 2

def OverT (D : Dat) (u : D.Pr.Word) (w : HeightOneSpectrum (𝓞 D.X.K)) : Prop := ((D.Pr.T u : ℕ) : 𝓞 D.X.K) ∈ w.asIdeal

end Chars

end GlobalTheory.IndefiniteRowSideFullHecke.ScalarCharacterTwist
