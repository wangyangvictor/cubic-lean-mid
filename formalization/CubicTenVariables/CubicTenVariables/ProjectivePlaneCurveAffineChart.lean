import TranslatedDepthSeven.HomogeneousConeStandardChart

/-!
# The standard affine chart of an integral projective plane curve

This is the elementary bridge needed after the fixed-pencil construction.
A homogeneous prime principal ideal of degree at least two cannot contain
the coordinate `X 0`.  The already proved projective-to-affine chart map
therefore sends it to a prime principal ideal.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace CubicTenVariables.ProjectivePlaneCurveAffineChart

open MvPolynomial
open TranslatedDepthSeven
attribute [local instance] MvPolynomial.gradedAlgebra

/-- On one fixed homogeneous degree, setting `X 0 = 1` loses no
information.  In particular a nonzero homogeneous equation has a nonzero
standard affine-chart equation. -/
theorem standardDehomogenization_ne_zero
    {K : Type*} [Field K] {n d : ℕ}
    (H : MvPolynomial (Fin (n + 1)) K) (hH : H.IsHomogeneous d)
    (hH0 : H ≠ 0) : standardDehomogenizationHom K n H ≠ 0 := by
  let E := MvPolynomial.renameEquiv K (_root_.finSuccEquiv n)
  have hEH : (E H).IsHomogeneous d := hH.rename_isHomogeneous
  intro hz
  have hcomp := standardDehomogenizationHom_comp_finSuccRename K n
  have happ := RingHom.congr_fun hcomp H
  have hdehom : multivariateDehomogenization (E H) = 0 := by
    simpa only [RingHom.comp_apply, hz, map_zero, E] using happ
  have heq : E H = 0 :=
    multivariateDehomogenization_injective_of_isHomogeneous hEH
      (isHomogeneous_zero _ _ d) hdehom
  exact hH0 (E.injective (by simpa only [map_zero] using heq))

/-- Dehomogenizing a geometrically integral projective plane equation in
the chart `X 0 = 1` gives an integral affine plane equation. -/
theorem standardDehomogenization_isDomain
    {K : Type*} [Field K] {d : ℕ} (hd : 2 ≤ d)
    (H : MvPolynomial (Fin 3) K) (hH : H.IsHomogeneous d)
    (hdeg : H.totalDegree = d)
    (hdom : IsDomain (MvPolynomial (Fin 3) K ⧸ Ideal.span {H})) :
    IsDomain (MvPolynomial (Fin 2) K ⧸
      Ideal.span {standardDehomogenizationHom K 2 H}) := by
  let I : Ideal (MvPolynomial (Fin 3) K) := Ideal.span {H}
  have hprime : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K) := by
    apply Ideal.homogeneous_span
    intro f hf
    rcases Set.mem_singleton_iff.mp hf with rfl
    exact ⟨d, hH⟩
  have hX : X (0 : Fin 3) ∉ I := by
    intro hmem
    have hdiv : H ∣ X (0 : Fin 3) := Ideal.mem_span_singleton.mp hmem
    have hle := totalDegree_le_of_dvd_of_isDomain hdiv (X_ne_zero (R := K) 0)
    rw [hdeg, totalDegree_X] at hle
    omega
  let E := MvPolynomial.renameEquiv K (_root_.finSuccEquiv 2)
  let J : Ideal (MvPolynomial (Option (Fin 2)) K) := I.map E
  obtain ⟨hJhom, hJprime, hJX⟩ :=
    finSuccRename_homogeneousPrime_avoids_none I hIhom hprime hX
  have hchart : (J.map multivariateDehomogenization.toRingHom).IsPrime :=
    map_multivariateDehomogenization_isPrime J hJhom hJprime hJX
  have hmap : J.map multivariateDehomogenization.toRingHom =
      I.map (standardDehomogenizationHom K 2) :=
    map_standardDehomogenizationHom_finSuccRename I
  rw [hmap] at hchart
  apply (Ideal.Quotient.isDomain_iff_prime _).mpr
  simpa only [I, Ideal.map_span, Set.image_singleton] using hchart

end CubicTenVariables.ProjectivePlaneCurveAffineChart
