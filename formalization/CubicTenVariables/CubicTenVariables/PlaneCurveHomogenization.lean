import CubicTenVariables.PrimeMultivariateHomogenization
import CubicTenVariables.Literature.FiniteFieldPointCounts
import TranslatedDepthSeven.DehomogenizationBaseChange

/-! Actual-degree projective closure of a geometrically integral affine
hypersurface. The statements use the literal principal ideals after
coefficient extension; no smoothness or point-count premise is introduced. -/

set_option autoImplicit false
noncomputable section
namespace CubicTenVariables.PlaneCurveHomogenization
open MvPolynomial TranslatedDepthSeven

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- Field extension does not change total degree. -/
theorem totalDegree_map (f : MvPolynomial (Fin n) K) :
    (map (algebraMap K L) f).totalDegree = f.totalDegree := by
  simp only [totalDegree, support_map_of_injective f (algebraMap K L).injective]

/-- Coefficient extension commutes with lossless fixed-degree homogenization. -/
theorem map_homogenization (f : MvPolynomial (Fin n) K) (d : ℕ)
    (hd : f.totalDegree ≤ d) :
    map (algebraMap K L) (multivariateHomogenization f d) =
      multivariateHomogenization (map (algebraMap K L) f) d := by
  apply multivariateDehomogenization_injective_of_isHomogeneous
    ((multivariateHomogenization_isHomogeneous f d).map (algebraMap K L))
    (multivariateHomogenization_isHomogeneous _ d)
  have h := DFunLike.congr_fun
    (multivariateDehomogenization_comp_map (σ := Fin n) (algebraMap K L))
    (multivariateHomogenization f d)
  change multivariateDehomogenization
      (map (algebraMap K L) (multivariateHomogenization f d)) =
    map (algebraMap K L) (multivariateDehomogenization
      (multivariateHomogenization f d)) at h
  rw [h, multivariateDehomogenization_homogenization f d hd,
    multivariateDehomogenization_homogenization _ d
      ((totalDegree_map f).trans_le hd)]

/-- An affine domain stays a domain on its actual-degree homogeneous closure,
over the same extension field. -/
theorem homogenization_quotient_isDomain
    (f : MvPolynomial (Fin n) K)
    (h : IsDomain (MvPolynomial (Fin n) L ⧸
      Ideal.span {map (algebraMap K L) f})) :
    IsDomain (MvPolynomial (Option (Fin n)) L ⧸
      Ideal.span {map (algebraMap K L)
        (multivariateHomogenization f f.totalDegree)}) := by
  apply (Ideal.Quotient.isDomain_iff_prime _).mpr
  rw [map_homogenization f f.totalDegree le_rfl]
  exact PrimeMultivariateHomogenization.isPrime _ _ (totalDegree_map f)
    ((Ideal.Quotient.isDomain_iff_prime _).mp h)

/-- Use ordinary `Fin (n+1)` coordinates, with coordinate zero homogenizing. -/
def closure (f : MvPolynomial (Fin n) K) : MvPolynomial (Fin (n+1)) K :=
  rename (finSuccEquiv n).symm (multivariateHomogenization f f.totalDegree)

/-- The projective closure is homogeneous of the actual affine degree. -/
theorem closure_isHomogeneous (f : MvPolynomial (Fin n) K) :
    (closure f).IsHomogeneous f.totalDegree :=
  (multivariateHomogenization_isHomogeneous f f.totalDegree).rename_isHomogeneous

/-- A nonzero affine equation has nonzero projective closure. -/
theorem closure_ne_zero (f : MvPolynomial (Fin n) K) (hf : f ≠ 0) :
    closure f ≠ 0 := by
  intro h
  have hz : multivariateHomogenization f f.totalDegree = 0 :=
    (renameEquiv K (finSuccEquiv n).symm).injective (by simpa [closure] using h)
  have hh := congrArg multivariateDehomogenization hz
  rw [multivariateDehomogenization_homogenization f f.totalDegree le_rfl,
    map_zero] at hh
  exact hf hh

/-- Geometric integrality of an affine hypersurface is preserved by its
literal projective closure. Positive degree excludes the zero equation. -/
theorem closure_geometricallyIntegral
    (f : MvPolynomial (Fin n) K) (hd : 1 ≤ f.totalDegree)
    (h : IsDomain (MvPolynomial (Fin n) (AlgebraicClosure K) ⧸
      Ideal.span {map (algebraMap K (AlgebraicClosure K)) f})) :
    Literature.GeometricallyIntegralForm (closure f) := by
  refine ⟨closure_ne_zero f ?_, ?_⟩
  · intro hz
    simp [hz] at hd
  · let E := renameEquiv (AlgebraicClosure K) (finSuccEquiv n).symm
    let I : Ideal (MvPolynomial (Option (Fin n)) (AlgebraicClosure K)) :=
      Ideal.span {map (algebraMap K (AlgebraicClosure K))
        (multivariateHomogenization f f.totalDegree)}
    letI : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp
      (homogenization_quotient_isDomain f h)
    apply (Ideal.Quotient.isDomain_iff_prime _).mpr
    have hp : (I.map E).IsPrime := inferInstance
    simpa only [I, Ideal.map_span, Set.image_singleton, E,
      renameEquiv_apply, closure, map_rename] using hp

end CubicTenVariables.PlaneCurveHomogenization
