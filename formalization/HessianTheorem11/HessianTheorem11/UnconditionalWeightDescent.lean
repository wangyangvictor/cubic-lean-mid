import HessianTheorem11.UnconditionalWeightFlags
import HessianTheorem11.ReducedRationalFlagDescent

/-! Rational positive-weight descent is proved without any GIT input:
finite-support optimization, a common splitting of two flags, strict
convexity, Galois invariance, and actual rational flag splitting suffice. -/
noncomputable section
namespace HessianTheorem11.UnconditionalWeightDescent
open MvPolynomial RationalDescent PolynomialRestriction
open UnconditionalWeightOptimization
variable {n d : ℕ}

theorem maximizing_flag_rational (F : RationalPolynomial n) (hne : F ≠ 0)
    (f : WeightFrame GeometricField n)
    (hf : MaximizingFrame (geometricPolynomial F) f) : f.RationalFlag := by
  intro σ
  have hc := maximizing_conjugate (geometricPolynomial F) f σ.toRingEquiv hf
  rw [show σ.toRingEquiv.toRingHom = σ.toRingHom from rfl,
    geometricPolynomial_galois_fixed F σ] at hc
  exact maximizing_flag_eq_of_norm_eq (geometricPolynomial F)
    (geometricPolynomial_ne_zero F hne) (f.conjugate σ.toRingEquiv) f hc hf rfl

/-- A homogeneous rational form admitting positive geometric weights
admits actual positive rational weights. No primitive normalization is
required for this existential conclusion. -/
theorem exists_rational_positive_frame (F : RationalPolynomial n)
    (hF : F.IsHomogeneous d) (hne : F ≠ 0)
    (hunstable : ∃ f : WeightFrame GeometricField n, f.Positive (geometricPolynomial F)) :
    ∃ g : WeightFrame ℚ n, g.Positive F := by
  obtain ⟨f,hf⟩ := exists_maximizing_frame (geometricPolynomial F) (hF.map _)
    (geometricPolynomial_ne_zero F hne) hunstable
  have hfixed := maximizing_flag_rational F hne f hf
  obtain ⟨g,hweight,hflag⟩ := ReducedRationalDescent.rationalFlagDescent.split f hfixed
  have hflags : weightFlag f.matrix f.weight =
      weightFlag (g.matrix.map (algebraMap ℚ GeometricField)) f.weight := by
    rw [hweight] at hflag
    exact hflag.symm
  have hp := positiveWeights_of_same_weightFlag (geometricPolynomial F)
    f.matrix (g.matrix.map (algebraMap ℚ GeometricField)) f.weight f.injective hflags hf.1
  rw [← hweight] at hp
  change HasPositiveWeights (restrict (g.matrix.map (algebraMap ℚ GeometricField))
    (map (algebraMap ℚ GeometricField) F)) g.weight at hp
  rw [← map_restrict] at hp
  exact ⟨g,(positiveWeights_map_iff (algebraMap ℚ GeometricField)
    (restrict g.matrix F) g.weight).mp hp⟩

theorem geometric_weightSemistable_of_rational (F : RationalPolynomial n)
    (hF : F.IsHomogeneous d) (hne : F ≠ 0) (hsemi : WeightSemistable F) :
    WeightSemistable (geometricPolynomial F) := by
  intro B hB w hsum hp
  let f : WeightFrame GeometricField n := ⟨B,hB,w,hsum⟩
  obtain ⟨g,hg⟩ := exists_rational_positive_frame F hF hne ⟨f,hp⟩
  exact hsemi g.matrix g.injective g.weight g.sum_zero hg

theorem anisotropic_geometric_weightSemistable (F : AnisotropicCubic n) (hn : 0 < n) :
    WeightSemistable (geometricPolynomial F.polynomial) :=
  geometric_weightSemistable_of_rational F.polynomial F.homogeneous
    (anisotropic_polynomial_ne_zero hn F) (rational_weightSemistable F hn)

end HessianTheorem11.UnconditionalWeightDescent
