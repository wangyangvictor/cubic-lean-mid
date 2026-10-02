import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Exact

/-!
# Finite-dimensional exact sequences

This file isolates the elementary linear-algebra calculation used for the
residual conormal space.  It deliberately contains no algebraic geometry:
an injective first map, exactness in the middle, and a surjective second map
force the dimension of the first term to be the difference of the other two
dimensions.
-/

namespace TranslatedDepthSeven

noncomputable section

universe u v w x

variable {K : Type u} {W : Type v} {V : Type w} {Q : Type x}
  [Field K]
  [AddCommGroup W] [Module K W]
  [AddCommGroup V] [Module K V]
  [AddCommGroup Q] [Module K Q]
  [FiniteDimensional K V]

/-- Dimension additivity for a short exact sequence, stated using the three
properties of the two displayed linear maps. -/
theorem finrank_eq_sub_of_injective_exact_surjective
    (f : W →ₗ[K] V) (g : V →ₗ[K] Q)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Module.finrank K W = Module.finrank K V - Module.finrank K Q := by
  have hsum := LinearMap.finrank_range_add_finrank_ker g
  have hrange : Module.finrank K (LinearMap.range g) = Module.finrank K Q := by
    rw [LinearMap.range_eq_top.mpr hg, finrank_top]
  have hker : Module.finrank K (LinearMap.ker g) = Module.finrank K W := by
    rw [hfg.linearMap_ker_eq]
    exact LinearMap.finrank_range_of_inj hf
  omega

/-- Numerical form used when the ambient space has dimension `N` and the
quotient has dimension `N - r`.  The inequality `r ≤ N` is necessary for
this natural-number statement. -/
theorem finrank_eq_of_injective_exact_surjective_of_complementary_finranks
    (f : W →ₗ[K] V) (g : V →ₗ[K] Q)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) {N r : ℕ} (hrN : r ≤ N)
    (hV : Module.finrank K V = N)
    (hQ : Module.finrank K Q = N - r) :
    Module.finrank K W = r := by
  rw [finrank_eq_sub_of_injective_exact_surjective f g hf hfg hg, hV, hQ]
  omega

/-- In the same numerical situation, `r` independent vectors in the first
term span it.  This is the precise linear-algebra passage from a nonzero
selected Jacobian minor to spanning of the residual conormal space. -/
theorem span_eq_top_of_linearIndependent_of_complementary_exact_finranks
    (f : W →ₗ[K] V) (g : V →ₗ[K] Q)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) {N r : ℕ} (hrN : r ≤ N)
    (hV : Module.finrank K V = N)
    (hQ : Module.finrank K Q = N - r)
    (v : Fin r → W) (hv : LinearIndependent K v) :
    Submodule.span K (Set.range v) = ⊤ := by
  letI : FiniteDimensional K W := FiniteDimensional.of_injective f hf
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card hv, Fintype.card_fin,
    finrank_eq_of_injective_exact_surjective_of_complementary_finranks
      f g hf hfg hg hrN hV hQ]

end

end TranslatedDepthSeven
