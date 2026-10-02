import HessianTheorem11.ReducedRelativeKempf

/-! The zero-target case of retained relative Kempf optimality supplies the
positive-weight rational descent needed by the cubic arguments.  This bypasses
the separate `TextbookOptimalFlags` input; it does not construct that entire
minimum-monomial-weight optimization interface or identify its objective with
the relative ideal order.  No orbit local-closedness input is needed for {0}.

References: the zero-target optimality is the case described by Dolgachev,
Lectures on Invariant Theory (2003), §9.5, Theorem 9.4, p.140.  Here it is deduced
from the already retained geometric relative theorem using actual order,
specialization, canonical parabolics, and proved Galois/rational flag descent.
-/
noncomputable section
namespace HessianTheorem11.ReducedZeroInstability
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
open RationalDescent ReducedRelative ReducedFlagStabilizer ReducedOrbitCoordinates
open ReducedWeightCurve
variable {K : Type*} [Field K] {n d : ℕ}

theorem coefficientClosed_zero :
    coefficientClosed ({0} : Set (MvPolynomial (Fin n) K)) := by
  intro F hF
  apply Set.mem_singleton_iff.mpr
  ext e
  have hz := hF (X e) (by
    intro G hG
    rcases Set.mem_singleton_iff.mp hG with rfl
    simp only [eval_X,coeff_zero])
  simpa only [eval_X,coeff_zero] using hz

theorem slInvariant_zero : slInvariant ({0} : Set (MvPolynomial (Fin n) K)) := by
  intro A _ F hF
  rcases Set.mem_singleton_iff.mp hF with rfl
  change restrict A 0 = 0
  exact map_zero (aeval (linearForms A))

theorem conjugateSet_zero (σ : K ≃+* K) :
    conjugateSet σ ({0} : Set (MvPolynomial (Fin n) K)) = {0} := by
  simp only [conjugateSet,Set.image_singleton,map_zero]

theorem zeroWeightPart_eq_zero_of_positive (F : MvPolynomial (Fin n) K)
    (w : Fin n → ℤ) (hF : HasPositiveWeights F w) : zeroWeightPart F w = 0 := by
  ext e
  rw [coeff_zeroWeightPart,coeff_zero]
  by_cases he : coeff e F = 0
  · simp only [he,ite_self]
  · have hp := hF e (Finsupp.mem_support_iff.mpr he)
    rw [if_neg (ne_of_gt hp)]

theorem zero_mem_orbitClosure_of_positive [Infinite K]
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (f : WeightFrame K n) (hf : f.Positive F) : 0 ∈ slOrbitClosure F := by
  have hW : HasNonnegativeWeights (restrict f.matrix F) f.weight :=
    fun e he => (hf e he).le
  have hz := zeroWeightPart_mem_slOrbitClosure (restrict f.matrix F) f.weight f.sum_zero hW
  rw [zeroWeightPart_eq_zero_of_positive _ _ hf] at hz
  have hunit : IsUnit f.matrix.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp f.injective)
  have hinv : IsUnit f.matrix⁻¹.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.isUnit_nonsing_inv_iff.mpr (Matrix.mulVec_injective_iff_isUnit.mp f.injective))
  have h := slOrbitClosure_restrict f.matrix⁻¹ hinv (restrict f.matrix F) 0
    (homogeneous_restrict _ F hF) hz
  rw [restrict_restrict,Matrix.mul_nonsing_inv f.matrix hunit,restrict_one] at h
  simpa only [restrict,map_zero] using h

/-- Positive relative order for the zero target forces strict positivity of
every supported monomial, using the proved actual specialization criterion. -/
theorem positive_of_zero_relativeOptimal (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous d) (hne : F ≠ 0) (f : WeightFrame K n)
    (hf : RelativeOptimal d F {0} f) : f.Positive F := by
  have hnot : F ∉ ({0} : Set (MvPolynomial (Fin n) K)) := by
    simpa only [Set.mem_singleton_iff] using hne
  have hs := (relativeOrder_pos_iff F hF {0} coefficientClosed_zero hnot f).mp
    hf.positive_order
  have he : originalCurve F f 0 = 0 := Set.mem_singleton_iff.mp hs
  rw [originalCurve_zero F f hf.admissible] at he
  have hz := congrArg (restrict f.matrix) he
  rw [restrict_restrict,Matrix.nonsing_inv_mul f.matrix
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp f.injective)),
    restrict_one] at hz
  have hzero : zeroWeightPart (restrict f.matrix F) f.weight = 0 := by
    simpa only [restrict,map_zero] using hz
  by_contra hp
  exact zeroWeightPart_ne_zero_of_not_positive _ _ hf.admissible hp hzero

theorem zero_optimal_rationalFlag (RK : RelativeKempfInput GeometricField)
    (F : RationalPolynomial n) (hF : F.IsHomogeneous d) (hne : F ≠ 0)
    (hzero : (0 : GeometricPolynomial n) ∈ slOrbitClosure (geometricPolynomial F))
    (f : WeightFrame GeometricField n)
    (hf : RelativeOptimal d (geometricPolynomial F) {0} f) : f.RationalFlag := by
  intro σ
  have hc := hf.conjugate σ.toRingEquiv (geometricPolynomial F) (hF.map _) _ f
  rw [conjugateSet_zero, show σ.toRingEquiv.toRingHom = σ.toRingHom from rfl,
    geometricPolynomial_galois_fixed F σ] at hc
  have hnot : geometricPolynomial F ∉ ({0} : Set (GeometricPolynomial n)) := by
    simpa only [Set.mem_singleton_iff] using geometricPolynomial_ne_zero F hne
  have he := RK.unique_parabolic (geometricPolynomial F) (hF.map _) {0}
    coefficientClosed_zero slInvariant_zero (by
      intro G hG
      rcases Set.mem_singleton_iff.mp hG with rfl
      exact hzero) hnot (f.conjugate σ.toRingEquiv) f hc hf
  exact weightFlag_eq_of_stabilizer_eq (f.conjugate σ.toRingEquiv).matrix f.matrix
    (f.conjugate σ.toRingEquiv).injective f.injective f.weight he

/-- Rational positive-weight descent from the zero-target specialization of
the retained geometric relative theorem.  The output is an actual rational
frame with primitive weights and strict positivity, not a rationality input. -/
theorem exists_rational_positive_frame (RK : RelativeKempfInput GeometricField)
    (F : RationalPolynomial n) (_hd : 0 < d) (hF : F.IsHomogeneous d)
    (hne : F ≠ 0)
    (hunstable : ∃ f : WeightFrame GeometricField n, f.Positive (geometricPolynomial F)) :
    ∃ g : WeightFrame ℚ n, g.Primitive ∧ g.Positive F := by
  obtain ⟨a,ha⟩ := hunstable
  have hzero := zero_mem_orbitClosure_of_positive (geometricPolynomial F) (hF.map _) a ha
  have hnot : geometricPolynomial F ∉ ({0} : Set (GeometricPolynomial n)) := by
    simpa only [Set.mem_singleton_iff] using geometricPolynomial_ne_zero F hne
  obtain ⟨f,hf⟩ := RK.exists_optimal (geometricPolynomial F) (hF.map _) {0}
    coefficientClosed_zero slInvariant_zero (Set.singleton_nonempty _) (by
      intro G hG
      rcases Set.mem_singleton_iff.mp hG with rfl
      exact hzero) hnot
  have hfixed := zero_optimal_rationalFlag RK F hF hne hzero f hf
  have hpositive := positive_of_zero_relativeOptimal (geometricPolynomial F) (hF.map _)
    (geometricPolynomial_ne_zero F hne) f hf
  obtain ⟨g,hweight,hflag⟩ := ReducedRationalDescent.rationalFlagDescent.split f hfixed
  have hflags : weightFlag f.matrix f.weight =
      weightFlag (g.matrix.map (algebraMap ℚ GeometricField)) f.weight := by
    rw [hweight] at hflag
    exact hflag.symm
  have hp := positiveWeights_of_same_weightFlag (geometricPolynomial F)
    f.matrix (g.matrix.map (algebraMap ℚ GeometricField)) f.weight f.injective hflags hpositive
  rw [← hweight] at hp
  change HasPositiveWeights (restrict (g.matrix.map (algebraMap ℚ GeometricField))
    (map (algebraMap ℚ GeometricField) F)) g.weight at hp
  rw [← map_restrict] at hp
  refine ⟨g, ?_, (positiveWeights_map_iff (algebraMap ℚ GeometricField)
    (restrict g.matrix F) g.weight).mp hp⟩
  unfold WeightFrame.Primitive
  rw [hweight]
  exact hf.primitive

/-- Geometric weight semistability follows from rational weight semistability,
using only retained RK and proved descent. -/
theorem geometric_weightSemistable_of_rational (RK : RelativeKempfInput GeometricField)
    (F : RationalPolynomial n) (hd : 0 < d) (hF : F.IsHomogeneous d)
    (hne : F ≠ 0) (hsemi : WeightSemistable F) :
    WeightSemistable (geometricPolynomial F) := by
  intro B hB w hsum hp
  let f : WeightFrame GeometricField n := ⟨B,hB,w,hsum⟩
  obtain ⟨g,_,hg⟩ := exists_rational_positive_frame RK F hd hF hne ⟨f,hp⟩
  exact hsemi g.matrix g.injective g.weight g.sum_zero hg

/-- The anisotropy implication is a consequence of the separately proved
rational anisotropy argument and general zero-target descent. -/
theorem anisotropic_geometric_weightSemistable (RK : RelativeKempfInput GeometricField)
    (F : AnisotropicCubic n) (hn : 0 < n) :
    WeightSemistable (geometricPolynomial F.polynomial) :=
  geometric_weightSemistable_of_rational RK F.polynomial (by norm_num) F.homogeneous
    (anisotropic_polynomial_ne_zero hn F) (rational_weightSemistable F hn)

end HessianTheorem11.ReducedZeroInstability
