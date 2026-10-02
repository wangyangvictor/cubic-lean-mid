import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Surjectivity from the first infinitesimal neighbourhood

This file records the elementary filtered-ring argument used at a rational
point.  A homomorphism of augmented algebras which is onto modulo the square
of the augmentation ideal is already onto after quotienting the target by a
power of that ideal.  The proof is the finite geometric-series argument on
the powers of the augmentation ideal; it uses neither local dimension nor a
regular-local-ring theorem.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v w

section Approximation

variable {B : Type u} {C : Type v} [CommRing B] [CommRing C]

/-- Approximation of the `e`-th power of `J` by the image of the `e`-th
power of `I`, with error one step deeper in the `J`-adic filtration. -/
def IdealPowerApproximation (g : B →+* C) (I : Ideal B) (J : Ideal C)
    (e : ℕ) : Prop :=
  ∀ x : C, x ∈ J ^ e → ∃ y : B, y ∈ I ^ e ∧ x - g y ∈ J ^ (e + 1)

private theorem map_mem_ideal_pow
    (g : B →+* C) (I : Ideal B) (J : Ideal C)
    (hIJ : I ≤ J.comap g) {e : ℕ} {y : B} (hy : y ∈ I ^ e) :
    g y ∈ J ^ e := by
  have hy' : g y ∈ (I ^ e).map g := Ideal.mem_map_of_mem g hy
  rw [Ideal.map_pow] at hy'
  exact (Ideal.pow_right_mono ((Ideal.map_le_iff_le_comap).2 hIJ) e) hy'

/-- First-order approximation propagates multiplicatively to every positive
power. -/
theorem idealPowerApproximation_succ
    (g : B →+* C) (I : Ideal B) (J : Ideal C)
    (hIJ : I ≤ J.comap g)
    (hfirst : IdealPowerApproximation g I J 1) :
    ∀ d : ℕ, IdealPowerApproximation g I J (d + 1) := by
  intro d
  induction d with
  | zero => simpa using hfirst
  | succ d ih =>
      intro x hx
      change x ∈ J ^ ((d + 1) + 1) at hx
      rw [pow_succ'] at hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro a ha b hb
        obtain ⟨a', ha'I, ha'⟩ := hfirst a (by simpa using ha)
        obtain ⟨b', hb'I, hb'⟩ := ih b hb
        refine ⟨a' * b', ?_, ?_⟩
        · rw [pow_succ']
          exact Ideal.mul_mem_mul (by simpa using ha'I) hb'I
        · rw [map_mul]
          have hga' : g a' ∈ J := by
            simpa using
            map_mem_ideal_pow g I J hIJ ha'I
          have h₁ : (a - g a') * b ∈ J ^ ((d + 1) + 1 + 1) := by
            have hraw : (a - g a') * b ∈ J ^ 2 * J ^ (d + 1) :=
              Ideal.mul_mem_mul ha' hb
            rw [← pow_add] at hraw
            simpa only [smul_eq_mul, Nat.add_assoc, Nat.reduceAdd,
              Nat.add_comm, Nat.add_left_comm] using hraw
          have h₂ : g a' * (b - g b') ∈ J ^ ((d + 1) + 1 + 1) := by
            rw [show (d + 1) + 1 + 1 = (d + 2) + 1 by omega,
              pow_succ']
            exact Ideal.mul_mem_mul hga' hb'
          change a * b - g a' * g b' ∈ J ^ ((d + 1) + 1 + 1)
          convert add_mem h₁ h₂ using 1
          ring
      · intro x y hx hy
        obtain ⟨x', hx'I, hx'⟩ := hx
        obtain ⟨y', hy'I, hy'⟩ := hy
        refine ⟨x' + y', add_mem hx'I hy'I, ?_⟩
        rw [map_add]
        convert add_mem hx' hy' using 1
        ring

end Approximation

section Surjectivity

variable {K : Type u} {B : Type v} {C : Type w}
variable [Field K] [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]

/-- A morphism of augmented algebras is surjective onto a nilpotent
infinitesimal neighbourhood as soon as it is surjective to first order.

The hypothesis `hfirst` is deliberately elementwise.  In applications it
is exactly surjectivity of the map modulo the squares of the two displayed
augmentation ideals. -/
theorem AlgHom.surjective_of_augmented_firstOrder_of_pow_ker_eq_bot
    (g : B →ₐ[K] C) (fB : B →ₐ[K] K) (fC : C →ₐ[K] K)
    (hcomp : fC.comp g = fB) (n : ℕ)
    (hnil : RingHom.ker fC.toRingHom ^ (n + 1) = ⊥)
    (hfirst : ∀ x : C, x ∈ RingHom.ker fC.toRingHom →
      ∃ y : B, y ∈ RingHom.ker fB.toRingHom ∧
        x - g y ∈ RingHom.ker fC.toRingHom ^ 2) :
    Function.Surjective g := by
  let I : Ideal B := RingHom.ker fB.toRingHom
  let J : Ideal C := RingHom.ker fC.toRingHom
  have hIJ : I ≤ J.comap g := by
    intro y hy
    change fC (g y) = 0
    rw [← AlgHom.comp_apply, hcomp]
    exact hy
  have happroxOne : IdealPowerApproximation g.toRingHom I J 1 := by
    intro x hx
    simpa [I, J] using hfirst x (by simpa [J] using hx)
  have happrox : ∀ d : ℕ,
      IdealPowerApproximation g.toRingHom I J (d + 1) :=
    idealPowerApproximation_succ g.toRingHom I J hIJ happroxOne
  have hliftKer : ∀ x : C, x ∈ J → ∃ y : B, g y = x := by
    intro x hx
    have hiter : ∀ d : ℕ, ∃ y : B, x - g y ∈ J ^ (d + 1) := by
      intro d
      induction d with
      | zero =>
          exact ⟨0, by simpa using hx⟩
      | succ d ih =>
          obtain ⟨y, hy⟩ := ih
          obtain ⟨z, -, hz⟩ := happrox d (x - g y) hy
          refine ⟨y + z, ?_⟩
          simpa only [map_add, sub_add_eq_sub_sub] using hz
    obtain ⟨y, hy⟩ := hiter n
    have : x - g y = 0 := by
      rw [hnil] at hy
      exact hy
    exact ⟨y, sub_eq_zero.mp this |>.symm⟩
  intro x
  have hx : x - algebraMap K C (fC x) ∈ J := by
    change fC (x - algebraMap K C (fC x)) = 0
    simp
  obtain ⟨y, hy⟩ := hliftKer (x - algebraMap K C (fC x)) hx
  refine ⟨y + algebraMap K B (fC x), ?_⟩
  rw [map_add, hy, g.commutes]
  simp

end Surjectivity

end

end TranslatedDepthSeven
