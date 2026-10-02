import HessianTheorem11.ReducedClosedOrbitKempf

/-! The zero orbit is closed, so closed-orbit Kempf alone gives the exact
positive-weight descent and geometric semistability consequences. Neither CO,
OG nor arbitrary-target RK is an input to these proofs. -/
noncomputable section
namespace HessianTheorem11.ReducedClosedOrbit
open MvPolynomial PolynomialRestriction PolynomialWeightTransport NonzeroLimitTransport
open RationalDescent ReducedRelative ReducedFlagStabilizer ReducedZeroInstability
variable {K : Type*} [Field K] {n d : ℕ}

theorem isClosedOrbit_zero : IsClosedOrbit ({0} : Set (MvPolynomial (Fin n) K)) := by
  refine ⟨coefficientClosed_zero, 0, ?_⟩
  ext F
  constructor
  · rintro rfl
    exact self_mem_slOrbit 0
  · rintro ⟨A,_,rfl⟩
    simp only [restrict,map_zero,Set.mem_singleton_iff]

theorem zero_optimal_rationalFlag (CK : ClosedOrbitKempfInput GeometricField)
    (F : RationalPolynomial n) (hF : F.IsHomogeneous d) (hne : F ≠ 0)
    (hzero : (0 : GeometricPolynomial n) ∈ slOrbitClosure (geometricPolynomial F))
    (f : WeightFrame GeometricField n)
    (hf : RelativeOptimal d (geometricPolynomial F) {0} f) : f.RationalFlag := by
  apply closedOrbit_optimal_rationalFlag CK F hF {0} isClosedOrbit_zero
    (by simpa only [Set.singleton_subset_iff] using hzero)
    (by simpa only [Set.mem_singleton_iff] using geometricPolynomial_ne_zero F hne)
    (fun σ => conjugateSet_zero σ.toRingEquiv) f hf

/-- Actual rational positive-frame descent from closed-orbit Kempf. -/
theorem exists_rational_positive_frame (CK : ClosedOrbitKempfInput GeometricField)
    (F : RationalPolynomial n) (_hd : 0 < d) (hF : F.IsHomogeneous d)
    (hne : F ≠ 0)
    (hunstable : ∃ f : WeightFrame GeometricField n, f.Positive (geometricPolynomial F)) :
    ∃ g : WeightFrame ℚ n, g.Primitive ∧ g.Positive F := by
  obtain ⟨a,ha⟩ := hunstable
  have hzero := zero_mem_orbitClosure_of_positive (geometricPolynomial F) (hF.map _) a ha
  have hnot : geometricPolynomial F ∉ ({0} : Set (GeometricPolynomial n)) := by
    simpa only [Set.mem_singleton_iff] using geometricPolynomial_ne_zero F hne
  obtain ⟨f,hf⟩ := CK.exists_optimal (geometricPolynomial F) (hF.map _) {0}
    isClosedOrbit_zero (by simpa only [Set.singleton_subset_iff] using hzero) hnot
  have hfixed := zero_optimal_rationalFlag CK F hF hne hzero f hf
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

theorem geometric_weightSemistable_of_rational (CK : ClosedOrbitKempfInput GeometricField)
    (F : RationalPolynomial n) (hd : 0 < d) (hF : F.IsHomogeneous d)
    (hne : F ≠ 0) (hsemi : WeightSemistable F) :
    WeightSemistable (geometricPolynomial F) := by
  intro B hB w hsum hp
  let f : WeightFrame GeometricField n := ⟨B,hB,w,hsum⟩
  obtain ⟨g,_,hg⟩ := exists_rational_positive_frame CK F hd hF hne ⟨f,hp⟩
  exact hsemi g.matrix g.injective g.weight g.sum_zero hg

theorem anisotropic_geometric_weightSemistable (CK : ClosedOrbitKempfInput GeometricField)
    (F : AnisotropicCubic n) (hn : 0 < n) :
    WeightSemistable (geometricPolynomial F.polynomial) :=
  geometric_weightSemistable_of_rational CK F.polynomial (by norm_num) F.homogeneous
    (anisotropic_polynomial_ne_zero hn F) (rational_weightSemistable F hn)

end HessianTheorem11.ReducedClosedOrbit
