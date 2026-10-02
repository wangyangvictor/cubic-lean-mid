import CubicTenVariables.Literature.ProperHyperplaneWeightDichotomy
import CubicTenVariables.SmallDegreeConeTraceCharacters
import CubicTenVariables.ConePrincipalOpen

/-! A vertical application of the explicitly assumed constant-coefficient
proper-hyperplane-family alternative to the actual cubic Fourier family. The previously
proved low-degree cone moment limit eliminates its large-moment alternative.
The resulting principal open is allowed to shrink. In particular, this file
does not assert the bound on every preselected smooth open, nor that the
discarded closed locus is homogeneous. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.SmallDegreeConeOpenTraceBound
open MvPolynomial HessianTheorem11 ProjectiveFourierIdentity
open TranslatedDepthSeven Filter FiniteFieldTraceCharacter PolynomialExponentialFamily
open scoped BigOperators Classical Topology
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual pointwise bounds on a single integral principal open. All choices
precede the prime, finite field, and nontrivial base character. The dimension
and weight relation makes the forbidden moment denominator exactly q^18. -/
theorem exists_open_bound
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
    (i : Fin 10) (hi : X i ∉ baseIdeal G) :
    ∃ (g : ParameterPolynomial 10) (N C : ℕ),
      map (Int.castRingHom ℚ) g ∉ baseIdeal G ∧ X i ∣ g ∧ 1 ≤ N ∧ 1 ≤ C ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
        ∀ (ψ : AddChar (ZMod p) ℂ), ψ ≠ 1 →
        ∀ (K : Type) [Field K] [Fintype K] [CharP K p]
          (v : Fin 10 → K), v ∈ parameterPoints G g K →
          ‖normalizedFourierSum (primeTraceCharacter p K ψ)
            (map (Int.castRingHom K) F) v‖ ≤
              (C : ℝ) * (Fintype.card K : ℝ)^((w : ℝ)/2) := by
  have hdim : ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸ baseIdeal G) = (r+1 : ℕ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hdegree.1
  obtain ⟨g,N₁,C,hg,hig,hN₁,hC,halt⟩ := dichotomy 10 3 t (r+1) F hF (by omega)
    G (X i) hprime hgeometric hdim (by simpa using hi)
  obtain ⟨N₂,hN₂,hdecay⟩ := SmallDegreeConeTraceCharacters.exists_decay
    degreeSpan smooth spread weil F hF hAn G r d hprime hgeometric hhom hdegree hsmall
  refine ⟨g,N₁*N₂,C,hg,hig,one_le_mul_of_one_le_of_one_le hN₁ hN₂,hC,?_⟩
  intro p _ hpN ψ hψ
  have hpN₁ : ¬ p ∣ N₁ := fun h => hpN (dvd_mul_of_dvd_left h N₂)
  have hpN₂ : ¬ p ∣ N₂ := fun h => hpN (dvd_mul_of_dvd_right h N₁)
  have hlimit := hdecay p hpN₂ (Extension p) ψ
    (fun a => parameterPoints G g (Extension p a)) hψ (extension_card p)
    (fun a _ v hv => ((mem_parameterPoints G g (Extension p a) v).mp hv).1)
  have hsum (a : ℕ) :
      (∑ v ∈ parameterPoints G g (Extension p a),
        ‖ProperHyperplaneFamily.defect F (Extension p a) v‖^2) =
      ∑ v ∈ parameterPoints G g (Extension p a),
        ‖normalizedFourierSum (primeTraceCharacter p (Extension p a) ψ)
          (map (Int.castRingHom (Extension p a)) F) v‖^2 := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [ProperHyperplaneFamily.normalizedFourierSum_eq_defect F hF (by omega) _
      (primeTraceCharacter_ne_one p (Extension p a) ψ hψ) v
      (parameterPoint_ne_zero_of_coordinate_dvd G g i hig v hv)]
  rcases halt p hpN₁ w with hbound | hlarge
  · intro K _ _ _ v hv
    rw [ProperHyperplaneFamily.normalizedFourierSum_eq_defect F hF (by omega) _
      (primeTraceCharacter_ne_one p K ψ hψ) v
      (parameterPoint_ne_zero_of_coordinate_dvd G g i hig v hv)]
    exact hbound K v hv
  · simp only [hweight, hsum] at hlarge
    have hev := hlimit.eventually (gt_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))
    obtain ⟨a,ha,hlt⟩ := (hlarge.and_eventually hev).exists
    exact False.elim (not_le_of_gt hlt ha)

/-- The same application with the initial nonzero coordinate constructed,
the proper closed residual and its dimension retained, and the literal
integer-frequency prime complete sum bounded. The new residual need not
be homogeneous; that is a subsequent stratification obligation. -/
theorem exists_complete_sum_bound
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
    (hsmall : r+d ≤ 8) (hweight : r+1+w+1 = 18) :
    ∃ (g : ParameterPolynomial 10) (N C : ℕ),
      map (Int.castRingHom ℚ) g ∉ baseIdeal G ∧ 1 ≤ N ∧ 1 ≤ C ∧
      ringKrullDim (MvPolynomial (Fin 10) ℚ ⧸
        ConePrincipalOpen.residualIdeal (baseIdeal G) (map (Int.castRingHom ℚ) g)) ≤
          (r : WithBot ℕ∞) ∧
      PrimeSpectrum.zeroLocus (ConePrincipalOpen.residualIdeal (baseIdeal G)
        (map (Int.castRingHom ℚ) g) : Set (MvPolynomial (Fin 10) ℚ)) ⊂
          PrimeSpectrum.zeroLocus (baseIdeal G : Set (MvPolynomial (Fin 10) ℚ)) ∧
      ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ N →
        ∀ v : Fin 10 → ℤ,
          (fun i => (v i : ZMod p)) ∈ parameterPoints G g (ZMod p) →
          ‖completeCubicSum F p v‖ ≤ (C : ℝ)*(p : ℝ)^((w : ℝ)/2+1) := by
  obtain ⟨i,hi⟩ := ConePrincipalOpen.exists_coordinate_not_mem 9 r
    (baseIdeal G) hprime hdegree.1
  obtain ⟨g,N,C,hg,_hig,hN,hC,hbound⟩ := exists_open_bound
    degreeSpan smooth spread weil dichotomy F hF hAn G r d w
    hprime hgeometric hhom hdegree hsmall hweight i hi
  refine ⟨g,N,C,hg,hN,hC,
    ConePrincipalOpen.residual_dimension_le _ hprime _ hg r hdegree.1,
    ConePrincipalOpen.residual_zeroLocus_ssubset _ hprime _ hg,?_⟩
  intro p _ hpN v hv
  have hb := hbound p hpN ZMod.stdAddChar (PrimeSumAdapter.stdAddChar_ne_one p)
    (ZMod p) (fun i => (v i : ZMod p)) hv
  rw [ZMod.card] at hb
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [SmallDegreeConeTraceCharacters.completeCubicSum_eq_prime_mul_normalized
    (by omega : 1 ≤ 10), norm_mul, Complex.norm_natCast]
  calc
    (p : ℝ)*_ ≤ (p : ℝ)*((C : ℝ)*(p : ℝ)^((w : ℝ)/2)) :=
      mul_le_mul_of_nonneg_left hb hp.le
    _ = (C : ℝ)*(p : ℝ)^((w : ℝ)/2+1) := by
      rw [Real.rpow_add hp, Real.rpow_one]
      ring

end CubicTenVariables.SmallDegreeConeOpenTraceBound
