import TranslatedDepthSeven.AffineDegreeOneHyperplaneInternal
import Mathlib.RingTheory.DedekindDomain.PID

/-!
# Full affine-line equality for degree-one prime curves

The filtered Hilbert argument puts every affine-linear equation through two
points in the prime ideal.  Consequently all coordinate classes are affine
linear in one separating coordinate.  The induced polynomial-ring map is
injective: a nonzero prime ideal in a polynomial ring in one variable is
maximal, whereas the two given evaluations have different values on its
variable.  Thus every real parameter, not just every selected integral
point, belongs to the original zero locus.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 2000000

/-- Two distinct scalar-valued evaluations of the variable force a map
from a univariate polynomial ring to a domain to be injective. -/
theorem polynomialAlgHom_injective_of_two_distinct_evaluations
    {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (theta : Polynomial K →ₐ[K] A) (ex ey : A →ₐ[K] K)
    (hxy : ex (theta Polynomial.X) ≠ ey (theta Polynomial.X)) :
    Function.Injective theta := by
  apply (RingHom.injective_iff_ker_eq_bot theta.toRingHom).mpr
  by_contra hnonzero
  let J := RingHom.ker theta.toRingHom
  have hprime : J.IsPrime := RingHom.ker_isPrime theta.toRingHom
  have hmax : J.IsMaximal := hprime.isMaximal hnonzero
  have hle : J ≤ RingHom.ker (ex.comp theta).toRingHom := by
    intro f hf
    change ex (theta f) = 0
    rw [show theta f = 0 from hf, map_zero]
  have heq : J = RingHom.ker (ex.comp theta).toRingHom :=
    hmax.eq_of_le (RingHom.ker_ne_top _) hle
  let f : Polynomial K := Polynomial.X - Polynomial.C (ex (theta Polynomial.X))
  have hf : f ∈ J := by
    rw [heq]
    change ex (theta f) = 0
    simp [f, Polynomial.C_eq_algebraMap]
  have h := congrArg ey (show theta f = 0 from hf)
  have hyx : ey (theta Polynomial.X) = ex (theta Polynomial.X) := by
    apply sub_eq_zero.mp
    simpa only [f, map_sub, Polynomial.C_eq_algebraMap,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, map_zero] using h
  exact hxy hyx.symm

/-- The complete zero locus of an affine Hilbert-degree-one prime curve,
once two distinct points are displayed, is exactly their affine line. -/
theorem affineIdealZeroLocus_eq_line_of_affineHilbert_degree_one
    {K : Type*} [Field K] {N : ℕ}
    (I : Ideal (MvPolynomial (Fin N) K))
    (hHilbert : HasAffineHilbertDimensionDegree I 1 1)
    (x y : Fin N → K) (hx : x ∈ affineIdealZeroLocus I)
    (hy : y ∈ affineIdealZeroLocus I) (hxy : x ≠ y) :
    affineIdealZeroLocus I =
      Set.range (fun s : K ↦ fun j ↦ x j + s * (y j - x j)) := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  have hdi : y i - x i ≠ 0 := sub_ne_zero.mpr hi.symm
  let b (j : Fin N) : K := (y j - x j) / (y i - x i)
  let a (j : Fin N) : K := x j - b j * x i
  let f (j : Fin N) : MvPolynomial (Fin N) K := X j - C (a j) - C (b j) * X i
  have hfdegree (j : Fin N) : (f j).totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (by rw [totalDegree_X])
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  have hfx (j : Fin N) : MvPolynomial.eval x (f j) = 0 := by
    simp only [f, map_sub, map_mul, eval_X, eval_C, a]
    ring
  have hfy (j : Fin N) : MvPolynomial.eval y (f j) = 0 := by
    simp only [f, map_sub, map_mul, eval_X, eval_C, a, b]
    field_simp [hdi]
    <;> ring
  have hfI (j : Fin N) : f j ∈ I :=
    linear_mem_prime_of_affineHilbert_degree_one_of_two_points
      I hHilbert x y hx hy hxy (f j) (hfdegree j) (hfx j) (hfy j)
  have hcoord (z : Fin N → K) (hz : z ∈ affineIdealZeroLocus I) (j : Fin N) :
      z j = a j + b j * z i := by
    have h := hz (f j) (hfI j)
    simp only [f, map_sub, map_mul, eval_X, eval_C] at h
    linear_combination h
  letI : I.IsPrime := hHilbert.1
  let A := MvPolynomial (Fin N) K ⧸ I
  let q : MvPolynomial (Fin N) K →ₐ[K] A := Ideal.Quotient.mkₐ K I
  let theta : Polynomial K →ₐ[K] A := Polynomial.aeval (q (X i))
  let pi : MvPolynomial (Fin N) K →ₐ[K] Polynomial K :=
    MvPolynomial.aeval fun j ↦ Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X
  have hC (c : K) : q (C c) = algebraMap K A c := q.commutes c
  have hqcoord (j : Fin N) :
      q (X j) = algebraMap K A (a j) + algebraMap K A (b j) * q (X i) := by
    have h : q (f j) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hfI j)
    simp only [f, map_sub, map_mul, hC] at h
    linear_combination h
  have hcomp : theta.comp pi = q := by
    apply MvPolynomial.algHom_ext
    intro j
    change theta (pi (X j)) = q (X j)
    simp only [pi, MvPolynomial.aeval_X, theta, map_add, map_mul,
      Polynomial.aeval_C, Polynomial.aeval_X]
    exact (hqcoord j).symm
  let ex : A →ₐ[K] K := affineIdealPointToQuotientAlgHom I ⟨x, hx⟩
  let ey : A →ₐ[K] K := affineIdealPointToQuotientAlgHom I ⟨y, hy⟩
  have hex : ex (q (X i)) = x i := by
    change MvPolynomial.aeval x (X i) = x i
    exact MvPolynomial.aeval_X x i
  have hey : ey (q (X i)) = y i := by
    change MvPolynomial.aeval y (X i) = y i
    exact MvPolynomial.aeval_X y i
  have htheta : Function.Injective theta := by
    apply polynomialAlgHom_injective_of_two_distinct_evaluations theta ex ey
    simpa only [theta, Polynomial.aeval_X, hex, hey] using hi
  have hpi (g : MvPolynomial (Fin N) K) (hg : g ∈ I) : pi g = 0 := by
    apply htheta
    rw [map_zero]
    have h := AlgHom.congr_fun hcomp g
    exact h.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hg)
  have hline (t : K) : (fun j ↦ a j + b j * t) ∈ affineIdealZeroLocus I := by
    have heval : (Polynomial.aeval t).comp pi =
        MvPolynomial.aeval (fun j ↦ a j + b j * t) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [pi]
    intro g hg
    have h := AlgHom.congr_fun heval g
    change (Polynomial.aeval t) (pi g) =
      MvPolynomial.aeval (fun j ↦ a j + b j * t) g at h
    rw [show pi g = 0 from hpi g hg, map_zero] at h
    exact h.symm
  ext z
  constructor
  · intro hz
    refine ⟨(z i - x i) / (y i - x i), ?_⟩
    funext j
    rw [hcoord z hz j]
    dsimp [a, b]
    field_simp [hdi]
    <;> ring
  · rintro ⟨s, rfl⟩
    have hpath : (fun j ↦ a j + b j * (x i + s * (y i - x i))) =
        (fun j ↦ x j + s * (y j - x j)) := by
      funext j
      dsimp [a, b]
      field_simp [hdi]
      <;> ring
    change (fun j ↦ x j + s * (y j - x j)) ∈ affineIdealZeroLocus I
    rw [← hpath]
    exact hline _

end

end TranslatedDepthSeven
