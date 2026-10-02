import TranslatedDepthSeven.ProjectiveBertiniIncidenceProjectiveChart
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! Dehomogenizing an actual radical homogeneous ideal remains radical.
This concerns the literal chart quotient, including an empty chart. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CubicTenVariables.HomogeneousRadicalChart
open MvPolynomial TranslatedDepthSeven
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type*} [Field K] {n : ℕ}

theorem isRadical
    (I : Ideal (MvPolynomial (Option (Fin n)) K))
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Option (Fin n)) K))
    (hrad : I.IsRadical) :
    (I.map multivariateDehomogenization.toRingHom).IsRadical := by
  intro f hf
  obtain ⟨m, hm⟩ := hf
  cases m with
  | zero =>
    have hone : (1 : MvPolynomial (Fin n) K) ∈
        I.map multivariateDehomogenization.toRingHom := by simpa using hm
    simpa using (I.map multivariateDehomogenization.toRingHom).mul_mem_left f hone
  | succ m =>
    let g := multivariateHomogenization f f.totalDegree
    have hg : g.IsHomogeneous f.totalDegree := multivariateHomogenization_isHomogeneous _ _
    have hdehom : multivariateDehomogenization g = f :=
      multivariateDehomogenization_homogenization f f.totalDegree le_rfl
    have hpow : multivariateDehomogenization (g ^ (m+1)) ∈
        I.map multivariateDehomogenization.toRingHom := by
      simpa only [map_pow, hdehom] using hm
    obtain ⟨a, ha⟩ := bertini_homogeneous_dehomogenization_mem_clears_coordinate
      I hhom (g ^ (m+1)) (hg.pow _) hpow
    have hmem : X (none : Option (Fin n)) ^ a * g ∈ I := by
      apply hrad
      refine ⟨m+1, ?_⟩
      have hh := I.mul_mem_left (X (none : Option (Fin n)) ^ (a*m)) ha
      convert hh using 1 <;> ring
    have hh := Ideal.mem_map_of_mem multivariateDehomogenization.toRingHom hmem
    change multivariateDehomogenization (X (none : Option (Fin n)) ^ a * g) ∈
      I.map multivariateDehomogenization.toRingHom at hh
    simpa only [map_mul, map_pow, multivariateDehomogenization_X_none,
      one_pow, one_mul, hdehom] using hh

end CubicTenVariables.HomogeneousRadicalChart
