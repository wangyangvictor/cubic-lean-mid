import TranslatedDepthSeven.QbarInvariantIdealDescent
import TranslatedDepthSeven.ConcreteExceptionalLocus
import TranslatedDepthSeven.GaloisMinimalComponentFrontier

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {σ : Type u}

theorem eval_coefficientExtension_at_rationalPoint
    (f : MvPolynomial σ ℚ) (x : σ → ℚ) :
    MvPolynomial.eval (fun i ↦ algebraMap ℚ Qbar (x i))
        (MvPolynomial.map (algebraMap ℚ Qbar) f) =
      algebraMap ℚ Qbar (MvPolynomial.eval x f) := by
  rw [← MvPolynomial.eval₂_eq_eval_map]
  simpa [MvPolynomial.eval₂_id] using
    (MvPolynomial.eval₂_comp_left (algebraMap ℚ Qbar)
      (RingHom.id ℚ) x f).symm

/-- Exact compatibility of rational zeroes with coefficient extension to
`Qbar`.  This is the point-set bridge needed after invariant-component
descent; it contains no dimension or degree assertion. -/
theorem rational_zero_of_ideal_iff_qbar_zero_of_extension
    (I : Ideal (MvPolynomial σ ℚ))
    (P : Ideal (MvPolynomial σ Qbar))
    (hIP : I.map (MvPolynomial.map (algebraMap ℚ Qbar)) = P)
    (x : σ → ℚ) :
    x ∈ affineIdealZeroLocus I ↔
      (fun i ↦ algebraMap ℚ Qbar (x i)) ∈ affineIdealZeroLocus P := by
  rw [mem_affineIdealZeroLocus_iff, mem_affineIdealZeroLocus_iff]
  constructor
  · intro hx
    rw [← hIP]
    change I.map (MvPolynomial.map (algebraMap ℚ Qbar)) ≤
      RingHom.ker (MvPolynomial.eval
        (fun i ↦ algebraMap ℚ Qbar (x i)))
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    change MvPolynomial.eval (fun i ↦ algebraMap ℚ Qbar (x i))
      (MvPolynomial.map (algebraMap ℚ Qbar) f) = 0
    rw [eval_coefficientExtension_at_rationalPoint, hx f hf, map_zero]
  · intro hx f hf
    have hmf : MvPolynomial.map (algebraMap ℚ Qbar) f ∈ P := by
      rw [← hIP]
      exact Ideal.mem_map_of_mem _ hf
    have := hx _ hmf
    rw [eval_coefficientExtension_at_rationalPoint] at this
    exact (map_eq_zero_iff (algebraMap ℚ Qbar)
      (FaithfulSMul.algebraMap_injective ℚ Qbar)).mp this

/-- Static component dichotomy at a rational point.  In the invariant case
the actual component descends to a homogeneous rational ideal with exactly
the same rational points.  Otherwise the point lies on a literal minimal
component of a strictly lower-dimensional conjugate intersection. -/
theorem rationalComponent_descends_or_lowerDimensionalFrontier
    [Fintype σ]
    (J : Ideal (MvPolynomial σ ℚ))
    {P : Ideal (MvPolynomial σ Qbar)} {s : ℕ}
    (hP : P ∈ finiteMinimalPrimes
      (J.map (MvPolynomial.map (algebraMap ℚ Qbar))))
    (hPhom : P.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ Qbar))
    (hPdim : ringKrullDim (MvPolynomial σ Qbar ⧸ P) = s)
    (x : σ → ℚ)
    (hx : P ≤ RingHom.ker (MvPolynomial.eval
      (fun i ↦ algebraMap ℚ Qbar (x i)))) :
    (∃ I : Ideal (MvPolynomial σ ℚ),
        I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ ℚ) ∧
        I.map (MvPolynomial.map (algebraMap ℚ Qbar)) = P ∧
        (x ∈ affineIdealZeroLocus I ↔
          (fun i ↦ algebraMap ℚ Qbar (x i)) ∈
            affineIdealZeroLocus P)) ∨
      ∃ g : Qbar ≃ₐ[ℚ] Qbar,
        ∃ L ∈ finiteMinimalPrimes (P ⊔ conjugateIdeal g P),
          P < L ∧ conjugateIdeal g P < L ∧
          L ≤ RingHom.ker (MvPolynomial.eval
            (fun i ↦ algebraMap ℚ Qbar (x i))) ∧
          ringKrullDim (MvPolynomial σ Qbar ⧸ L) < s := by
  rcases rationalMinimalComponent_fixed_or_lowerDimensionalFrontier
      J hP hPdim x hx with hstable | hfrontier
  · left
    obtain ⟨I, hIhom, hIP⟩ :=
      rationalHomogeneousIdeal_descent_of_galoisInvariant P hstable hPhom
    exact ⟨I, hIhom, hIP,
      rational_zero_of_ideal_iff_qbar_zero_of_extension I P hIP x⟩
  · exact Or.inr hfrontier

end

end TranslatedDepthSeven
