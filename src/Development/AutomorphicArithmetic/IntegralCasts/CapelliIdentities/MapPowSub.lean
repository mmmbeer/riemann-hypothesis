import Mathlib

theorem UpperTheory.Reformulated.B.MapPowSub.map_pow_sub :
    ∀ {K : Type} [inst : Field K] {σ : K →+* ℂ} {V E : Type} [inst_1 : AddCommGroup V]
      [inst_2 : Module K V] [inst_3 : AddCommGroup E] [inst_4 : Module ℂ E] (f : V →ₛₗ[σ] E)
      (T : Module.End K V) (S : Module.End ℂ E),
      (∀ (v : V), f (T v) = S (f v)) →
        ∀ (a : K) (k : ℕ) (v : V), f (((T - a • 1) ^ k) v) = ((S - σ a • 1) ^ k) (f v) := by
  intro K _ σ V E _ _ _ _ f T S h a k
  have h1 : ∀ v : V, f ((T - a • (1 : Module.End K V)) v) = (S - σ a • (1 : Module.End ℂ E)) (f v) := by
    intro v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, h, LinearMap.map_smulₛₗ]
  induction k with
  | zero => intro v; simp only [pow_zero, Module.End.one_apply]
  | succ n ih =>
    intro v
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h1]
