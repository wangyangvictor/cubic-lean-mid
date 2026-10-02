import CubicTenVariables.PlaneCubicSingularGeometry
import CubicTenVariables.ProjectivePlaneCurveAffineChart
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# A geometrically irreducible ternary form is not a cylinder

A positive-degree binary form over an algebraically closed field has a
projective zero. If a ternary homogeneous form is independent of its first
coordinate, that binary zero supplies an entire hyperplane in its zero
locus. An irreducible polynomial containing a hyperplane has degree at most
one. Thus degree at least two excludes this cylindrical case.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace CubicTenVariables.FixedLeadingSurfaceDirectionDependence

open MvPolynomial TranslatedDepthSeven

variable {K : Type*} [Field K]

private def oneVariableEquiv : MvPolynomial (Fin 1) K ≃ₐ[K] Polynomial K :=
  (MvPolynomial.renameEquiv K
    (Equiv.equivPUnit (Fin 1) : Fin 1 ≃ PUnit.{1})).trans
    (MvPolynomial.pUnitAlgEquiv K)

private theorem oneVariableEquiv_C (c : K) :
    oneVariableEquiv (C c : MvPolynomial (Fin 1) K) = Polynomial.C c := by
  simp [oneVariableEquiv, MvPolynomial.pUnitAlgEquiv_apply]

private theorem eval_oneVariableEquiv (q : MvPolynomial (Fin 1) K) (t : K) :
    (oneVariableEquiv q).eval t = eval (fun _ ↦ t) q := by
  change Polynomial.eval₂ (RingHom.id K) t
    (MvPolynomial.pUnitAlgEquiv K
      (MvPolynomial.renameEquiv K
        (Equiv.equivPUnit (Fin 1) : Fin 1 ≃ PUnit.{1}) q)) = _
  rw [MvPolynomial.eval₂_const_pUnitAlgEquiv]
  simp only [MvPolynomial.renameEquiv_apply, eval₂_rename, Function.comp_def, eval₂_id]

private theorem standardDehomogenization_injective_on_homogeneous_degree
    {n d : ℕ} (F G : MvPolynomial (Fin (n + 1)) K)
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous d)
    (h : standardDehomogenizationHom K n F = standardDehomogenizationHom K n G) :
    F = G := by
  apply sub_eq_zero.mp
  by_contra hne
  apply ProjectivePlaneCurveAffineChart.standardDehomogenization_ne_zero
    (F - G) (hF.sub hG) hne
  rw [map_sub, h, sub_self]

/-- A binary homogeneous form of positive degree has a zero in one of
the two standard projective charts. This includes the zero form. -/
theorem binary_homogeneous_projective_zero [IsAlgClosed K]
    {d : ℕ} (hd : 0 < d) (H : MvPolynomial (Fin 2) K)
    (hH : H.IsHomogeneous d) :
    (∃ a : K, eval ![1, a] H = 0) ∨ eval ![0, 1] H = 0 := by
  let q := standardDehomogenizationHom K 1 H
  let p := oneVariableEquiv q
  by_cases hp : p.degree = 0
  · right
    have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_degree_eq_zero hp
    have hq : q = C (p.coeff 0) := by
      apply oneVariableEquiv.injective
      rw [oneVariableEquiv_C]
      exact hpC
    have hHform : H = C (p.coeff 0) * X (0 : Fin 2) ^ d := by
      apply standardDehomogenization_injective_on_homogeneous_degree H _ hH
        (isHomogeneous_C_mul_X_pow _ _ d)
      change q = _
      rw [hq]
      simp [standardDehomogenizationHom]
    rw [hHform]
    simp [hd.ne']
  · left
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hp
    refine ⟨a, ?_⟩
    have he := eval_oneVariableEquiv q a
    rw [eval_standardDehomogenizationHom] at he
    have hc : (Fin.cases 1 (fun _ : Fin 1 ↦ a) : Fin 2 → K) = ![1, a] := by
      ext i
      fin_cases i <;> rfl
    simpa only [p, Polynomial.IsRoot.def, he, hc] using ha

/-- Over an algebraically closed field, an irreducible ternary form of
degree at least two depends on its first variable. -/
theorem degreeOf_zero_pos_of_irreducible_homogeneous [IsAlgClosed K]
    {d : ℕ} (hd : 2 ≤ d) (F : MvPolynomial (Fin 3) K)
    (hF : F.IsHomogeneous d) (hirr : Irreducible F) :
    0 < F.degreeOf 0 := by
  by_contra hnot
  have hdeg0 : F.degreeOf 0 = 0 := by omega
  let H := (MvPolynomial.finSuccEquiv K 2 F).coeff 0
  have hH : H.IsHomogeneous d := hF.finSuccEquiv_coeff_isHomogeneous 0 d (by omega)
  have hP : MvPolynomial.finSuccEquiv K 2 F = Polynomial.C H := by
    apply Polynomial.eq_C_of_natDegree_eq_zero
    rwa [natDegree_finSuccEquiv]
  have heval (t : K) (a : Fin 2 → K) : eval (Fin.cons t a) F = eval a H := by
    rw [eval_eq_eval_mv_eval', hP]
    simp
  have hFdegree : F.totalDegree = d := hF.totalDegree hirr.ne_zero
  obtain (⟨a, ha⟩ | ha) := binary_homogeneous_projective_zero (by omega) H hH
  · let ell : (Fin 3 → K) →ₗ[K] K := LinearMap.proj 2 - a • LinearMap.proj 1
    have hell : ell ≠ 0 := by
      intro hz
      have h := LinearMap.congr_fun hz ![0, 0, 1]
      simp [ell] at h
    have hle := PlaneCubicSingularGeometry.degree_le_one_of_vanishes_on_hyperplane
      F hirr ell hell (by
        intro x hx
        have hx' : x 2 = a * x 1 := by
          simpa only [ell, LinearMap.sub_apply, LinearMap.proj_apply,
            LinearMap.smul_apply, smul_eq_mul, sub_eq_zero] using hx
        have hvec : x = Fin.cons (x 0) ((x 1) • ![1, a]) := by
          ext i
          refine Fin.cases (by simp) (fun j ↦ ?_) i
          simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul]
          fin_cases j <;> simp [hx', mul_comm]
        rw [hvec, heval]
        simpa only [eval₂_id, ha, mul_zero] using
          CubicGradientScaling.homogeneous_eval₂_smul H hH (RingHom.id K) ![1, a] (x 1))
    omega
  · let ell : (Fin 3 → K) →ₗ[K] K := LinearMap.proj 1
    have hell : ell ≠ 0 := by
      intro hz
      have h := LinearMap.congr_fun hz ![0, 1, 0]
      simp [ell] at h
    have hle := PlaneCubicSingularGeometry.degree_le_one_of_vanishes_on_hyperplane
      F hirr ell hell (by
        intro x hx
        have hx' : x 1 = 0 := hx
        have hvec : x = Fin.cons (x 0) ((x 2) • ![0, 1]) := by
          ext i
          refine Fin.cases (by simp) (fun j ↦ ?_) i
          simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul]
          fin_cases j <;> simp [hx']
        rw [hvec, heval]
        simpa only [eval₂_id, ha, mul_zero] using
          CubicGradientScaling.homogeneous_eval₂_smul H hH (RingHom.id K) ![0, 1] (x 2))
    omega

/-- Passing to a homogeneous component and extending coefficients cannot
create a variable which was absent from the original polynomial. -/
theorem degreeOf_map_homogeneousComponent_le
    {R L σ : Type*} [CommRing R] [CommRing L] (ρ : R →+* L)
    (g : MvPolynomial σ R) (d : ℕ) (i : σ) :
    (map ρ (homogeneousComponent d g)).degreeOf i ≤ g.degreeOf i := by
  classical
  rw [degreeOf_eq_sup, degreeOf_eq_sup]
  apply Finset.sup_mono
  intro μ hμ
  have hne := mem_support_iff.mp ((support_map_subset _ _) hμ)
  rw [coeff_homogeneousComponent] at hne
  split_ifs at hne with hdegree
  · exact mem_support_iff.mpr hne
  · exact (hne rfl).elim

/-- Geometric irreducibility of any degree-`d` homogeneous component,
with `d ≥ 2`, forces the full ternary polynomial to depend on the first
variable. In the surface application this component is the top form. -/
theorem degreeOf_zero_pos_of_geometrically_irreducible_topComponent
    {d : ℕ} (hd : 2 ≤ d) (g : MvPolynomial (Fin 3) K)
    (hirr : Irreducible (map (algebraMap K (AlgebraicClosure K))
      (homogeneousComponent d g))) : 0 < g.degreeOf 0 := by
  have hpos := degreeOf_zero_pos_of_irreducible_homogeneous hd
    _ ((homogeneousComponent_isHomogeneous d g).map _) hirr
  exact hpos.trans_le (degreeOf_map_homogeneousComponent_le _ g d 0)

end CubicTenVariables.FixedLeadingSurfaceDirectionDependence
