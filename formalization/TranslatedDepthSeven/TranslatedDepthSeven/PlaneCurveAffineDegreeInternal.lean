import TranslatedDepthSeven.FilteredAffinePlaneCurveMonomialsInternal
import TranslatedDepthSeven.ProjectiveAffineChartBridge
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! # The first-chart equation retains the degree of an integral plane curve

A loss of degree in a homogeneous equation after setting the first
coordinate equal to one would force that coordinate to divide the equation.
An irreducible equation of degree at least two therefore keeps its degree.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial

theorem totalDegree_multivariateDehomogenization_of_not_X_dvd
    {K : Type*} [Field K] {n δ : ℕ}
    (P : MvPolynomial (Option (Fin n)) K) (hP : P.IsHomogeneous δ)
    (hX : ¬ X (none : Option (Fin n)) ∣ P) :
    (multivariateDehomogenization P).totalDegree = δ := by
  obtain ⟨hdegree, hrecover⟩ :=
    multivariateHomogenization_dehomogenization_of_isHomogeneous P hP
  apply le_antisymm hdegree
  by_contra h
  have hgap : 0 < δ - (multivariateDehomogenization P).totalDegree := by omega
  have hfactor := multivariateHomogenization_raise_degree
    (multivariateDehomogenization P) le_rfl hdegree
  rw [hrecover] at hfactor
  apply hX
  rw [hfactor]
  exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _

theorem affinePlaneDehomogenization_eq_option_rename
    (K : Type*) [Field K] (P : MvPolynomial (Fin 3) K) :
    affinePlaneDehomogenization K P =
      multivariateDehomogenization
        ((MvPolynomial.renameEquiv K (_root_.finSuccEquiv 2)) P) := by
  have heq : affinePlaneDehomogenization K =
      multivariateDehomogenization.comp
        (MvPolynomial.renameEquiv K (_root_.finSuccEquiv 2)).toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [affinePlaneDehomogenization, multivariateDehomogenization,
        MvPolynomial.renameEquiv_apply]
  exact AlgHom.congr_fun heq P

theorem not_X_dvd_irreducible_plane_equation
    {K : Type*} [Field K] {δ : ℕ} (hδ : 2 ≤ δ)
    (P : MvPolynomial (Fin 3) K) (hP : P.IsHomogeneous δ)
    (hirr : Irreducible P) : ¬ X (0 : Fin 3) ∣ P := by
  intro hdiv
  have hXunit : ¬ IsUnit (X (0 : Fin 3) : MvPolynomial (Fin 3) K) := by
    intro hu
    have ht := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    simp at ht
  have hPX : P ∣ X (0 : Fin 3) :=
    ((hirr.dvd_iff.mp hdiv).resolve_left hXunit).dvd
  have ht := totalDegree_le_of_dvd_of_isDomain hPX (X_ne_zero _)
  rw [hP.totalDegree hirr.ne_zero] at ht
  simp only [totalDegree_X] at ht
  omega

/-- Both the nonzero condition needed for standard-monomial independence
and the exact degree needed by the weight calculation follow internally. -/
theorem affinePlaneDehomogenization_degree_of_irreducible
    {K : Type*} [Field K] {δ : ℕ} (hδ : 2 ≤ δ)
    (P : MvPolynomial (Fin 3) K) (hP : P.IsHomogeneous δ)
    (hirr : Irreducible P) :
    affinePlaneDehomogenization K P ≠ 0 ∧
      (affinePlaneDehomogenization K P).totalDegree = δ := by
  let e := MvPolynomial.renameEquiv K (_root_.finSuccEquiv 2)
  have heP : (e P).IsHomogeneous δ := by
    exact hP.rename_isHomogeneous
  have hX : ¬ X (none : Option (Fin 2)) ∣ e P := by
    intro h
    have hh := map_dvd e.symm h
    apply not_X_dvd_irreducible_plane_equation hδ P hP hirr
    simpa [e, MvPolynomial.renameEquiv_apply] using hh
  have hdegree := totalDegree_multivariateDehomogenization_of_not_X_dvd (e P) heP hX
  rw [← affinePlaneDehomogenization_eq_option_rename K P] at hdegree
  refine ⟨?_, hdegree⟩
  intro hz
  rw [hz, totalDegree_zero] at hdegree
  omega

end
end TranslatedDepthSeven
