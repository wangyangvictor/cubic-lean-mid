import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Homogeneous colon ideals and their stabilization

These elementary algebraic facts are the finite-ideal part of the standard
proof of Hilbert--Serre by induction on the number of polynomial variables.
Colon by a homogeneous form preserves homogeneity.  The ideals `I : G^e`
form an increasing sequence which stabilizes in a Noetherian ring; at a
stable term multiplication by `G` is injective on the quotient.

No Hilbert-polynomial existence, dimension, degree, or counting assertion is
assumed or concluded here.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1500000

/-- Colon by the principal ideal of a homogeneous form is homogeneous. -/
theorem homogeneous_colon_span_singleton
    {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ K))
    (G : MvPolynomial σ K) {k : ℕ} (hG : G.IsHomogeneous k) :
    (I.colon (Ideal.span ({G} : Set (MvPolynomial σ K)))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ K) := by
  classical
  intro n p hp
  apply Ideal.mem_colon_singleton.mpr
  have h := hI (n + k) (Ideal.mem_colon_singleton.mp hp)
  change (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ K)
    (p * G) (n + k) : MvPolynomial σ K) ∈ I at h
  rw [DirectSum.coe_decompose_mul_add_of_right_mem
    (MvPolynomial.homogeneousSubmodule σ K) hG] at h
  exact h

/-- The elementary identity between two successive principal colons. -/
theorem colon_span_pow_succ
    {R : Type*} [CommRing R] (I : Ideal R) (G : R) (e : ℕ) :
    (I.colon (Ideal.span ({G ^ e} : Set R))).colon (Ideal.span ({G} : Set R)) =
      I.colon (Ideal.span ({G ^ (e + 1)} : Set R)) := by
  ext p
  simp only [Ideal.mem_colon_singleton, pow_succ]
  rw [mul_assoc, mul_comm G (G ^ e)]

/-- The exact stabilization of `I : G^e`; the stable quotient has no
`G`-torsion.  This uses only the ascending chain condition on ideals. -/
theorem exists_stable_colon_span_pow
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (G : R) :
    ∃ e : ℕ,
      (∀ k ≥ e, I.colon (Ideal.span ({G ^ k} : Set R)) =
        I.colon (Ideal.span ({G ^ e} : Set R))) ∧
      (I.colon (Ideal.span ({G ^ e} : Set R))).colon (Ideal.span ({G} : Set R)) =
        I.colon (Ideal.span ({G ^ e} : Set R)) := by
  let chain : ℕ →o Ideal R :=
    { toFun := fun e ↦ I.colon (Ideal.span ({G ^ e} : Set R))
      monotone' := monotone_nat_of_le_succ (by
        intro e
        rw [← colon_span_pow_succ]
        exact Ideal.le_colon) }
  obtain ⟨e, he⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance chain
  refine ⟨e, fun k hk ↦ (he k hk).symm, ?_⟩
  rw [colon_span_pow_succ]
  exact (he (e + 1) (by omega)).symm

end
end TranslatedDepthSeven
