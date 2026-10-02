import CubicTenVariables.IntegralConeNormalization

/-! Two elementary bridges for replacing a principal open by a positive
homogeneous-component open. The component choice concerns the literal
integral polynomial, and the finite-field scalar is obtained by a proved
univariate root bound. No geometric or literature input is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CubicTenVariables.HomogeneousComponentOpen
open MvPolynomial DavenportHomogeneity
open scoped BigOperators

/-- A polynomial divisible by a coordinate has zero constant component. -/
theorem constant_component_eq_zero {σ R : Type*} [CommSemiring R]
    (g : MvPolynomial σ R) (i : σ) (hig : X i ∣ g) :
    homogeneousComponent 0 g = 0 := by
  obtain ⟨q,rfl⟩ := hig
  rw [homogeneousComponent_zero]
  change C (constantCoeff (X i*q)) = 0
  simp

/-- A polynomial nonzero modulo any rational ideal has a positive-degree
homogeneous component still nonzero modulo that ideal, if a coordinate
divides the original polynomial. Homogeneity of the ideal is unnecessary. -/
theorem exists_positive_component {σ : Type*}
    (I : Ideal (MvPolynomial σ ℚ)) (g : MvPolynomial σ ℤ) (i : σ)
    (hg : map (Int.castRingHom ℚ) g ∉ I) (hig : X i ∣ g) :
    ∃ j : ℕ, 0 < j ∧ j ≤ g.totalDegree ∧
      map (Int.castRingHom ℚ) (homogeneousComponent j g) ∉ I ∧
      (homogeneousComponent j g).IsHomogeneous j := by
  classical
  have hex : ∃ j ∈ Finset.range (g.totalDegree+1),
      map (Int.castRingHom ℚ) (homogeneousComponent j g) ∉ I := by
    by_contra h
    push_neg at h
    apply hg
    rw [← g.sum_homogeneousComponent, map_sum]
    exact I.sum_mem (fun j hj => h j hj)
  obtain ⟨j,hj,hnot⟩ := hex
  have hj0 : j ≠ 0 := by
    intro heq
    subst j
    rw [constant_component_eq_zero g i hig, map_zero] at hnot
    exact hnot I.zero_mem
  exact ⟨j,Nat.pos_of_ne_zero hj0,by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj,
    hnot,homogeneousComponent_isHomogeneous j g⟩

/-- The scalar-substitution polynomial has degree no larger than the
original total degree, including when the substitution becomes zero. -/
theorem scaling_natDegree_le {σ K : Type*} [Field K]
    (g : MvPolynomial σ K) (v : σ → K) :
    (homogeneousScalingHom v g).natDegree ≤ g.totalDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [homogeneousScalingHom_coeff, homogeneousComponent_eq_zero j g hj, map_zero]

/-- A nonvanishing homogeneous component supplies a nonzero scalar on
which the original polynomial does not vanish, over any sufficiently
large finite field. -/
theorem exists_nonzero_scalar {σ K : Type*} [Field K] [Fintype K]
    (g : MvPolynomial σ K) (v : σ → K) (j : ℕ)
    (hj : eval v (homogeneousComponent j g) ≠ 0)
    (hcard : g.totalDegree+1 < Fintype.card K) :
    ∃ a : K, a ≠ 0 ∧ eval (a • v) g ≠ 0 := by
  classical
  let P := homogeneousScalingHom v g
  have hP : P ≠ 0 := by
    intro h
    apply hj
    rw [← homogeneousScalingHom_coeff]
    change P.coeff j = 0
    rw [h, Polynomial.coeff_zero]
  have hdeg : P.natDegree < Fintype.card Kˣ := by
    rw [Fintype.card_units]
    have hd := scaling_natDegree_le g v
    change P.natDegree ≤ g.totalDegree at hd
    omega
  have hex : ∃ a : Kˣ, P.eval (a : K) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
      Units.val_injective h hdeg)
  obtain ⟨a,ha⟩ := hex
  refine ⟨a,a.ne_zero,?_⟩
  simpa only [P, eval_homogeneousScalingHom] using ha

/-- Integral-coefficient form with one degree cutoff fixed before the
characteristic, finite field, and point. -/
theorem exists_nonzero_scalar_integer {σ K : Type*} [Field K] [Fintype K]
    (g : MvPolynomial σ ℤ) (v : σ → K) (j : ℕ)
    (hj : eval v (map (Int.castRingHom K) (homogeneousComponent j g)) ≠ 0)
    (hcard : g.totalDegree+1 < Fintype.card K) :
    ∃ a : K, a ≠ 0 ∧ eval (a • v) (map (Int.castRingHom K) g) ≠ 0 := by
  apply exists_nonzero_scalar (map (Int.castRingHom K) g) v j
  · simpa only [IntegralConeNormalization.map_homogeneousComponent] using hj
  · exact lt_of_le_of_lt (Nat.add_le_add_right (Finset.sup_mono (support_map_subset _ _)) 1) hcard

end CubicTenVariables.HomogeneousComponentOpen
