import HessianTheorem11.ReducedHypersurfacePartials
import HessianTheorem11.ReducedStrictDimension
import HessianTheorem11.KernelAnnihilatorGeometry

/-! The full old hypersurface-dimension interface follows from retained
generic smoothness/rank and proved commutative algebra. No hypersurface or
strict-dimension-drop premise remains. -/

noncomputable section
namespace HessianTheorem11.ReducedHypersurfaceDimension
open MvPolynomial Module

theorem hypersurface (GR : GenericRankOpenInput) {n : ℕ}
    (P : GeometricPolynomial n) (hP : Irreducible P) :
    affineDimension (polynomialHypersurface P) = ((n - 1 : ℕ) : Dimension) := by
  classical
  obtain ⟨i, hi⟩ := ReducedHypersurfacePartials.exists_nonzero_partial P hP
  let I : Ideal (GeometricPolynomial n) := Ideal.span {P}
  letI : I.IsPrime := (Ideal.span_singleton_prime hP.ne_zero).mpr hP.prime
  have hnot : pderiv i P ∉ I := by
    intro h
    exact ReducedHypersurfacePartials.not_dvd_partial P i hi
      (Ideal.mem_span_singleton.mp h)
  obtain ⟨x, hx, hpx⟩ := exists_zeroLocus_eval_ne_zero I (pderiv i P) hnot
  obtain ⟨G⟩ := GR.choose (polynomialHypersurface P) (polynomialHypersurface_closed P)
    (polynomialHypersurface_irreducible P hP) (fun _ : Fin 0 => (0 : GeometricPolynomial n))
    (0 : GeometricPoint n →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
  obtain ⟨y, hy, hpy⟩ := exists_on_dense_set_eval_ne_zero G.dense (pderiv i P)
    ⟨x, hx P (Ideal.mem_span_singleton_self P), hpx⟩
  let L := polynomialDifferential P y
  have hL : L ≠ 0 := by
    intro hzero
    have he := LinearMap.congr_fun hzero (Pi.single i 1)
    apply hpy
    simpa [L, polynomialDifferential_apply, Pi.single_apply] using he
  have hrange : LinearMap.range L = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.surjective_iff_ne_zero.mpr hL)
  have hdim := L.finrank_range_add_finrank_ker
  rw [hrange] at hdim
  simp only [finrank_top, finrank_self, finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hdim
  have htan := affineTangentSpace_irreducible_hypersurface_eq_ker P hP y (G.subset hy)
  rw [← polynomialHypersurface_eq_zeroLocus] at htan
  have hsmooth := G.smooth y hy
  rw [htan] at hsmooth
  change 1 + finrank GeometricField (LinearMap.ker (polynomialDifferential P y)) = n at hdim
  rw [G.dimension_base]
  congr 1
  omega

/-- The complete original AD interface, now a theorem from GR alone. -/
theorem affineHypersurfaceDimensionInput (GR : GenericRankOpenInput) :
    AffineHypersurfaceDimensionInput where
  hypersurface := hypersurface GR
  proper_closed := ReducedStrictDimension.proper_closed

end HessianTheorem11.ReducedHypersurfaceDimension
