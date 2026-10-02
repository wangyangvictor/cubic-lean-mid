import CubicTenVariables.HomogeneousConeTraceBound

/-! The trace open can avoid any prescribed homogeneous equation which
does not vanish identically on the cone. This supplies the exclusion of a
later closed stratum without needing any smooth/lisse metadata in the
downstream partition argument. The bound and its constants are unchanged. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.HomogeneousConeTraceRestriction
open MvPolynomial HessianTheorem11 ProjectiveFourierIdentity
open TranslatedDepthSeven FiniteFieldTraceCharacter PolynomialExponentialFamily
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

theorem eval_ne_zero_of_dvd {n : ℕ} (g h : ParameterPolynomial n) (hgh : g ∣ h)
    (K : Type*) [Field K] (v : Fin n → K)
    (hh : eval v (map (Int.castRingHom K) h) ≠ 0) :
    eval v (map (Int.castRingHom K) g) ≠ 0 := by
  obtain ⟨q,rfl⟩ := hgh
  have he :
    eval v (map (Int.castRingHom K) g) ≠ 0 ∧
      eval v (map (Int.castRingHom K) q) ≠ 0 := by
    simpa only [map_mul, eval_mul, mul_ne_zero_iff] using hh
  exact he.1

theorem parameterPoints_subset_of_dvd {n t : ℕ} (G : Fin t → ParameterPolynomial n)
    (g h : ParameterPolynomial n) (hgh : g ∣ h)
    (K : Type*) [Field K] [Fintype K] :
    parameterPoints G h K ⊆ parameterPoints G g K := by
  intro v hv
  obtain ⟨hG,hh⟩ := (mem_parameterPoints G h K v).mp hv
  exact (mem_parameterPoints G g K v).mpr ⟨hG,eval_ne_zero_of_dvd g h hgh K v hh⟩

/-- Multiplication by a prescribed homogeneous equation preserves the
dense homogeneous trace open and forces it to avoid that equation's zero
locus in every good characteristic. The existing hypotheses are unchanged. -/
theorem exists_bound_avoiding
    (degreeSpan : StandardAG.ProjectiveDegreeSpanInequality ℚ)
    (smooth : Literature.SmoothInfinityGeometricIntegrality)
    (spread : CubicGenericIntegralityUniform.Uniform)
    (weil : Literature.AffinePlaneCubicWeil)
    (dichotomy : Literature.ProperHyperplaneWeightDichotomy)
    (F : MvPolynomial (Fin 10) ℤ) (hF : F.IsHomogeneous 3)
    (hAn : Anisotropic (map (Int.castRingHom ℚ) F))
    {t : ℕ} (G : Fin t → MvPolynomial (Fin 10) ℤ) (r d w : ℕ)
    (hprime : (baseIdeal G).IsPrime)
    (hgeometric : ((baseIdeal G).map (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime)
    (hhom : (baseIdeal G).IsHomogeneous (homogeneousSubmodule (Fin 10) ℚ))
    (hdegree : Published.HasProjectiveDimensionDegree (baseIdeal G) r d)
    (hsmall : r+d ≤ 8) (hweight : r+1+w+1 = 18)
    (Q : ParameterPolynomial 10) (e : ℕ) (hQ : Q.IsHomogeneous e)
    (hQI : map (Int.castRingHom ℚ) Q ∉ baseIdeal G) :
    ∃ (h : ParameterPolynomial 10) (j N C : ℕ),
      0 < j ∧ h.IsHomogeneous j ∧ map (Int.castRingHom ℚ) h ∉ baseIdeal G ∧
      Q ∣ h ∧ 1 ≤ N ∧ 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
        ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 →
        ∀ (K : Type) [Field K] [Fintype K] [CharP K p]
          (v : Fin 10 → K), v ∈ parameterPoints G h K →
          ‖normalizedFourierSum (primeTraceCharacter p K ψ)
            (map (Int.castRingHom K) F) v‖ ≤
              (C : ℝ) * (Fintype.card K : ℝ)^((w : ℝ)/2) := by
  obtain ⟨h,j,N,C,hj,hh,hI,hN,hC,hbound⟩ := HomogeneousConeTraceBound.exists_bound
    degreeSpan smooth spread weil dichotomy F hF hAn G r d w
    hprime hgeometric hhom hdegree hsmall hweight
  have hnot : map (Int.castRingHom ℚ) (h*Q) ∉ baseIdeal G := by
    rw [map_mul]
    intro hmem
    exact (hprime.mem_or_mem hmem).elim hI hQI
  refine ⟨h*Q,j+e,N,C,by omega,hh.mul hQ,hnot,dvd_mul_left Q h,hN,hC,?_⟩
  intro p _ hp ψ hψ K _ _ _ v hv
  exact hbound p hp ψ hψ K v
    (parameterPoints_subset_of_dvd G h (h*Q) (dvd_mul_right h Q) K hv)

end CubicTenVariables.HomogeneousConeTraceRestriction
