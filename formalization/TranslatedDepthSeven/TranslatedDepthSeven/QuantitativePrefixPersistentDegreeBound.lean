import TranslatedDepthSeven.QuantitativePrefixPersistentCellAggregation
import TranslatedDepthSeven.ProperHomogeneousHypersurfaceComponentDegreeInternal

/-!
# Terminal degree bounds for the actual persistent root components

A nonempty persistent cell has the same geometric component at a full-depth
vertex as at the root.  Applying the internal proper-section degree bound to
that terminal cut bounds the already certified root degree.  In particular,
the larger root auxiliary degree need not be used for this individual bound.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000

/-- The certified degree of a nonempty persistent component is at most the
surface degree times a uniform terminal-cut degree cap.  All cuts and all
component labels are those of the literal quantitative prefix partition. -/
theorem quantitativePrefixPersistent_degree_le_terminalCap
    {d b K : ℕ}
    (sourceEquations : Finset (MvPolynomial (Fin 4) ℚ))
    (hgeometricPrime : ((finiteEquationIdeal sourceEquations).map
      (MvPolynomial.map (algebraMap ℚ Qbar))).IsPrime)
    (hdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal sourceEquations) 2 d)
    {P : Finset ℕ} {depth : ℕ}
    (u : IntVector 3) (m : ℕ) (X : Finset (IntVector 3))
    (allowed : IntVector 3 → Finset ℕ)
    (blockDegree : PrimeSubsetPrefix.Vertex P depth → ℕ)
    (auxiliary : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      (Fin 3 → ZMod (PrimeSubsetPrefix.modulus v)) →
        MvPolynomial (Fin 4) ℚ)
    (hallowed : ∀ z ∈ X, allowed z ⊆ P)
    (hroom : ∀ z ∈ X, depth ≤ (allowed z).card)
    (hauxiliary : ∀ z ∈ X, ∀ v ∈
        PrimeSubsetPrefix.survivingVertices P (allowed z) depth,
      (auxiliary v (integralResidueVector z)).IsHomogeneous
          (b + blockDegree v) ∧
        auxiliary v (integralResidueVector z) ∉
          finiteEquationIdeal sourceEquations)
    (hterminal : ∀ v : PrimeSubsetPrefix.Vertex P depth,
      v.1.card = depth → b + blockDegree v ≤ K)
    (Q : Ideal (MvPolynomial (Fin 4) Qbar)) (δ : ℕ)
    (hQprime : Q.IsPrime)
    (hQhom : Q.IsHomogeneous (homogeneousSubmodule (Fin 4) Qbar))
    (hQdegree : HasProjectiveDimensionDegree Q 1 δ)
    (hcell : (quantitativePrefixPersistentCell sourceEquations auxiliary
      u m X allowed (some Q)).Nonempty) :
    δ ≤ d * K := by
  classical
  obtain ⟨z, hz⟩ := hcell
  have hzX : z ∈ X := (Finset.mem_filter.mp hz).1
  have hpersistent := (Finset.mem_filter.mp hz).2.2
  obtain ⟨v, hv, hvdepth⟩ := exists_fullDepth_survivingPrefix
    P (allowed z) depth (hallowed z hzX) (hroom z hzX)
  let G := auxiliary v (integralResidueVector z)
  let E := qbarSurfaceEquationFamily sourceEquations
  let Gbar := MvPolynomial.map (algebraMap ℚ Qbar) G
  have hG := hauxiliary z hzX v hv
  have hEprime : (finiteEquationIdeal E).IsPrime := by
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact hgeometricPrime
  have hEdegree : HasProjectiveDimensionDegree
      (finiteEquationIdeal E) 2 d := by
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarHasProjectiveDimensionDegree_of_rational _ hdegree hgeometricPrime
  have hGhom : Gbar.IsHomogeneous (b + blockDegree v) :=
    hG.1.map (algebraMap ℚ Qbar)
  have hGnot : Gbar ∉ finiteEquationIdeal E := by
    rw [finiteEquationIdeal_qbarSurfaceEquationFamily]
    exact qbarMap_not_mem_extendedIdeal_of_not_mem _ G hG.2
  have hQminimal := (selectedFiniteEquationComponent_spec
    (quantitativePrefixCutEquations sourceEquations auxiliary z v)
    (quantitativePrefixCoordinate u m z) (hpersistent v hv)).1
  have hcontain : finiteEquationIdeal E ⊔ Ideal.span ({Gbar} : Set _) ≤ Q := by
    have hc := le_of_mem_finiteMinimalPrimes hQminimal
    change finiteEquationIdeal
      (finiteEquationFamilyUnion E {Gbar}) ≤ Q at hc
    rw [finiteEquationIdeal_union] at hc
    simpa only [finiteEquationIdeal, Finset.coe_singleton] using hc
  have hmass := sum_projectiveDegrees_proper_homogeneous_hypersurface_le
    (ι := Unit) (r := 1) (finiteEquationIdeal E) hEprime hEdegree
    Gbar hGhom hGnot (fun _ ↦ Q) (fun _ ↦ δ)
    (fun _ _ _ ↦ Subsingleton.elim _ _)
    (fun _ ↦ hQprime) (fun _ ↦ hQhom) (fun _ ↦ hQdegree)
    (fun _ ↦ hcontain)
  have hlocal : δ ≤ d * (b + blockDegree v) := by simpa using hmass
  exact hlocal.trans (Nat.mul_le_mul_left d (hterminal v hvdepth))

end

end TranslatedDepthSeven
