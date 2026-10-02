import TranslatedDepthSeven.ProjectiveBertiniSmoothCoordinateSection

/-!
# The generic hyperplane has a nonsingular minor at its marked point

The coefficient polynomial of the augmented Jacobian minor is nonzero:
specializing the hyperplane coefficients to one free coordinate recovers
the original minor. Injecting the coefficient ring into a field preserves
this certificate, including for an algebraic closure of its fraction field.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

/-- All affine hyperplanes through `z`, with independent literal
coefficient variables. -/
noncomputable def bertiniGenericMarkedHyperplane
    {K : Type*} [CommRing K] {N : ℕ} (z : Fin N → K) :
    MvPolynomial (Fin N) (MvPolynomial (Fin N) K) :=
  ∑ i : Fin N, C (X i) * (X i - C (C (z i)))

/-- The generic marked hyperplane prepended to the extended local
equations, with the two polynomial variable roles kept explicit. -/
noncomputable def bertiniGenericMarkedEquations
    {K : Type*} [CommRing K] {N c : ℕ}
    (equations : Fin c → MvPolynomial (Fin N) K) (z : Fin N → K) :
    Fin (c + 1) → MvPolynomial (Fin N) (MvPolynomial (Fin N) K) :=
  Fin.cons (bertiniGenericMarkedHyperplane z)
    (fun i ↦ MvPolynomial.map (C : K →+* MvPolynomial (Fin N) K) (equations i))

/-- The coordinate-axis specialization selects the corresponding
coordinate difference. -/
theorem bertiniGenericMarkedHyperplane_specialize_coordinate
    {K : Type*} [CommRing K] {N : ℕ} (z : Fin N → K) (j : Fin N) :
    MvPolynomial.map (eval (fun i : Fin N ↦ if i = j then 1 else 0))
      (bertiniGenericMarkedHyperplane z) = X j - C (z j) := by
  classical
  simp [bertiniGenericMarkedHyperplane, apply_ite]

/-- The selected minor of the generic hyperplane section has a nonzero
coefficient polynomial at the marked point. -/
theorem bertiniGenericMarkedHyperplane_selectedMinor_ne_zero
    {K : Type*} [Field K] {N c : ℕ}
    (equations : Fin c → MvPolynomial (Fin N) K)
    (cols : Fin c → Fin N) (z : Fin N → K)
    (j : Fin N) (hj : j ∉ Set.range cols)
    (hminor : eval z (selectedJacobianDeterminant equations cols) ≠ 0) :
    eval (fun i : Fin N ↦ C (z i))
      (selectedJacobianDeterminant
        (bertiniGenericMarkedEquations equations z) (Fin.cons j cols)) ≠ 0 := by
  classical
  let φ : MvPolynomial (Fin N) K →+* K :=
    eval (fun i : Fin N ↦ if i = j then 1 else 0)
  have hφC : φ.comp C = RingHom.id K := by
    ext a
    simp [φ]
  intro hzero
  have h := congrArg φ hzero
  rw [map_zero, MvPolynomial.map_eval, map_selectedJacobianDeterminant] at h
  have hmap : (fun i : Fin (c + 1) ↦ MvPolynomial.map φ
      (bertiniGenericMarkedEquations equations z i)) =
      Fin.cons (X j - C (z j)) equations := by
    funext i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · exact bertiniGenericMarkedHyperplane_specialize_coordinate z j
    · simp only [bertiniGenericMarkedEquations, Fin.cons_succ,
        MvPolynomial.map_map, hφC, MvPolynomial.map_id]
  rw [hmap, selectedJacobianDeterminant_cons_coordinateDifference equations cols j (z j) hj] at h
  have hpoint : (φ ∘ fun i : Fin N ↦ C (z i)) = z := by
    funext i
    simp [φ]
  rw [hpoint] at h
  exact hminor h

end
end TranslatedDepthSeven
