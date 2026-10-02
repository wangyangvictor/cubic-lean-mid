import TranslatedDepthSeven.ProjectiveBertiniIncidenceGlobal
import TranslatedDepthSeven.ProjectiveBertiniSmoothRegularPair
import TranslatedDepthSeven.ProjectiveBertiniSmoothPrincipalCover

/-!
# Integral universal hyperplane incidence through a marked smooth point

This theorem concerns the literal universal equation in the given affine
coordinate ring. It proves integrality of that ring. The further generic
fiber, geometric-integrality, and projective-section conclusions are not
part of its statement.
-/

namespace TranslatedDepthSeven

noncomputable section
open MvPolynomial

/-- The same conclusion at a specified smooth marked coordinate chart.
Keeping the marked point fixed permits the generic Jacobian calculation
to use exactly the same point and equations. -/
theorem marked_linear_incidence_isDomain_of_selectedJacobianChart
    {K : Type*} [Field K] {N c : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (hcols : Function.Injective cols)
    (u : MvPolynomial (Fin N) K)
    (hIJ : Ideal.span (Set.range equations) ≤ J)
    (hclear : ∀ f ∈ J, u * f ∈ Ideal.span (Set.range equations))
    (z : Fin N → K) (hz : J ≤ RingHom.ker (aeval z).toRingHom)
    (hminor : aeval z (u * selectedJacobianDeterminant equations cols) ≠ 0)
    (j k : Fin N) (hjk : j ≠ k)
    (hj : j ∉ Set.range cols) (hk : k ∉ Set.range cols) :
    IsDomain (MvPolynomial (Fin N) (MvPolynomial (Fin N) K ⧸ J) ⧸
      Ideal.span ({bertiniLinear (fun i : Fin N ↦
        Ideal.Quotient.mk J (X i - C (z i)))} : Set _)) := by
  letI : J.IsPrime := hJ
  obtain ⟨s, hs, ha, hb⟩ :=
    exists_principalOpen_regular_coordinate_pair_of_selectedJacobianChart
      J hJ equations cols hcols u hIJ hclear z hz hminor j k hjk hj hk
  have hs0 : s ≠ 0 := fun h ↦ hs (h ▸ map_zero _)
  have hcover := bertini_span_marked_denominator_coordinateDifferences_eq_top J z hz s hs
  exact bertini_linear_sum_isDomain_of_principal_regular_pair
    (fun i : Fin N ↦ Ideal.Quotient.mk J (X i - C (z i)))
    s hs0 hcover j k (Ne.symm hjk) ha hb

theorem exists_integral_marked_linear_incidence_of_primeAffine_dimension
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {N r : ℕ}
    (J : Ideal (MvPolynomial (Fin N) K)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ J) = (r : WithBot ℕ∞))
    (hr : 2 ≤ r) :
    ∃ (z : Fin N → K) (_hz : J ≤ RingHom.ker (aeval z).toRingHom),
      IsDomain (MvPolynomial (Fin N) (MvPolynomial (Fin N) K ⧸ J) ⧸
        Ideal.span ({bertiniLinear (fun i : Fin N ↦
          Ideal.Quotient.mk J (X i - C (z i)))} : Set _)) := by
  letI : J.IsPrime := hJ
  obtain ⟨z, hz, i, j, s, hij, hs, hi, hj⟩ :=
    exists_principalOpen_regular_coordinate_pair_of_primeAffine_dimension J hJ hdim hr
  have hs0 : s ≠ 0 := fun h ↦ hs (h ▸ map_zero _)
  have hcover := bertini_span_marked_denominator_coordinateDifferences_eq_top J z hz s hs
  exact ⟨z, hz, bertini_linear_sum_isDomain_of_principal_regular_pair
    (fun i : Fin N ↦ Ideal.Quotient.mk J (X i - C (z i)))
    s hs0 hcover i j (Ne.symm hij) hi hj⟩

end
end TranslatedDepthSeven
