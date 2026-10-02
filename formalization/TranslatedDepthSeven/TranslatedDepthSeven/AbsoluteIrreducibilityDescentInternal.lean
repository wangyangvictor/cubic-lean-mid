import TranslatedDepthSeven.AbsoluteIrreducibility

/-! Unit reflection and irreducibility descent for coefficient extension
between fields, specialized to the literal absolute irreducibility input. -/
namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

 theorem isUnit_of_mvPolynomial_coefficientMap
    {σ K L : Type*} [Field K] [Field L] (f : K →+* L)
    (P : MvPolynomial σ K) (hP : IsUnit (P.map f)) : IsUnit P := by
  classical
  obtain ⟨r, hr, heq⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hP
  have hcoeff : f (P.coeff 0) = r := by
    simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_C, if_pos rfl] using
      congrArg (fun Q ↦ Q.coeff 0) heq
  have hconstant : P = C (P.coeff 0) := by
    apply MvPolynomial.map_injective f f.injective
    rw [map_C, hcoeff, heq]
  have hc : IsUnit (P.coeff 0) := isUnit_iff_ne_zero.mpr (fun h ↦ hr.ne_zero (by
    rw [← hcoeff, h, map_zero]))
  rw [hconstant]
  exact hc.map C

 theorem irreducible_of_mvPolynomial_coefficientMap
    {σ K L : Type*} [Field K] [Field L] (f : K →+* L)
    (P : MvPolynomial σ K) (hP : Irreducible (P.map f)) : Irreducible P where
  not_isUnit hu := hP.not_isUnit (hu.map (MvPolynomial.map f))
  isUnit_or_isUnit := by
    rintro a b rfl
    exact (hP.isUnit_or_isUnit (map_mul (MvPolynomial.map f) a b)).imp
      (isUnit_of_mvPolynomial_coefficientMap f a)
      (isUnit_of_mvPolynomial_coefficientMap f b)

namespace Published
 theorem IsAbsolutelyIrreducible.irreducible {σ : Type*}
    {P : MvPolynomial σ ℚ} (hP : IsAbsolutelyIrreducible P) : Irreducible P :=
  irreducible_of_mvPolynomial_coefficientMap (algebraMap ℚ (AlgebraicClosure ℚ)) P hP
end Published
end
end TranslatedDepthSeven
