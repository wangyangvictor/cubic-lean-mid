import TranslatedDepthSeven.SmoothCurvePolynomialCoordinatesInternal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Filtration

/-!
# A one-dimensional smooth coordinate gives a formal-series embedding

Every coefficient is defined using one finite polynomial approximation.
Uniqueness of lower coefficients makes these approximations compatible and
proves the ring laws.  Krull separation in the original Noetherian domain
proves injectivity.  No completion identification is assumed.
-/

namespace TranslatedDepthSeven

noncomputable section

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  (f : A →ₐ[K] K) [Algebra.IsStandardSmoothOfRelativeDimension 1 K A]

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

def smoothCurvePolynomialApproximation (n : ℕ) (x : A) : Polynomial K :=
  (exists_smoothCurvePolynomialApproximation f x (n + 1) (by omega)).choose

theorem smoothCurvePolynomialApproximation_spec (n : ℕ) (x : A) :
    smoothCurvePolynomialCoordinate f (smoothCurvePolynomialApproximation f n x) - x ∈
      RingHom.ker f.toRingHom ^ (n + 1 + 1) :=
  (exists_smoothCurvePolynomialApproximation f x (n + 1) (by omega)).choose_spec

def smoothCurveSeries (x : A) : PowerSeries K :=
  PowerSeries.mk fun n ↦ (smoothCurvePolynomialApproximation f n x).coeff n

theorem smoothCurveSeries_coeff_of_approximation
    (x : A) (P : Polynomial K) (k : ℕ) (hk : 1 ≤ k)
    (hP : smoothCurvePolynomialCoordinate f P - x ∈ RingHom.ker f.toRingHom ^ (k + 1))
    (n : ℕ) (hn : n < k) : PowerSeries.coeff n (smoothCurveSeries f x) = P.coeff n := by
  let Q := smoothCurvePolynomialApproximation f n x
  let M := RingHom.ker f.toRingHom ^ (n + 1 + 1)
  have hP' : smoothCurvePolynomialCoordinate f P - x ∈ M :=
    Ideal.pow_le_pow_right (by omega) hP
  have hQ : smoothCurvePolynomialCoordinate f Q - x ∈ M :=
    smoothCurvePolynomialApproximation_spec f n x
  have hd : smoothCurvePolynomialCoordinate f (P - Q) ∈ M := by
    have h := M.sub_mem hP' hQ
    simpa only [map_sub, sub_sub_sub_cancel_right] using h
  have hc := smoothCurvePolynomialCoordinate_coeff_zero_of_mem f (P - Q)
    (n + 1) (by omega) hd n (by omega)
  have heq : P.coeff n = Q.coeff n := sub_eq_zero.mp (by simpa using hc)
  simpa only [smoothCurveSeries, PowerSeries.coeff_mk] using heq.symm

theorem smoothCurveSeries_zero : smoothCurveSeries f 0 = 0 := by
  ext n
  have h := smoothCurveSeries_coeff_of_approximation f 0 0 (n + 1) (by omega)
    (by simp) n (by omega)
  simpa only [Polynomial.coeff_zero, map_zero] using h

theorem smoothCurveSeries_one : smoothCurveSeries f 1 = 1 := by
  ext n
  have h := smoothCurveSeries_coeff_of_approximation f 1 1 (n + 1) (by omega)
    (by simp) n (by omega)
  simpa only [Polynomial.coeff_one, PowerSeries.coeff_one] using h

theorem smoothCurveSeries_add (x y : A) :
    smoothCurveSeries f (x + y) = smoothCurveSeries f x + smoothCurveSeries f y := by
  ext n
  let P := smoothCurvePolynomialApproximation f n x
  let Q := smoothCurvePolynomialApproximation f n y
  let M := RingHom.ker f.toRingHom ^ (n + 1 + 1)
  have hsum : smoothCurvePolynomialCoordinate f (P + Q) - (x + y) ∈ M := by
    have h := M.add_mem (smoothCurvePolynomialApproximation_spec f n x)
      (smoothCurvePolynomialApproximation_spec f n y)
    convert h using 1 <;> simp only [map_add] <;> abel
  rw [smoothCurveSeries_coeff_of_approximation f (x + y) (P + Q) (n + 1)
    (by omega) hsum n (by omega)]
  simp [smoothCurveSeries, P, Q]

theorem smoothCurveSeries_mul (x y : A) :
    smoothCurveSeries f (x * y) = smoothCurveSeries f x * smoothCurveSeries f y := by
  ext n
  let P := smoothCurvePolynomialApproximation f n x
  let Q := smoothCurvePolynomialApproximation f n y
  let M := RingHom.ker f.toRingHom ^ (n + 1 + 1)
  have hP : smoothCurvePolynomialCoordinate f P - x ∈ M :=
    smoothCurvePolynomialApproximation_spec f n x
  have hQ : smoothCurvePolynomialCoordinate f Q - y ∈ M :=
    smoothCurvePolynomialApproximation_spec f n y
  have hprod : smoothCurvePolynomialCoordinate f (P * Q) - x * y ∈ M := by
    have h := M.add_mem (M.mul_mem_left (smoothCurvePolynomialCoordinate f P) hQ)
      (M.mul_mem_right y hP)
    convert h using 1 <;> simp only [map_mul] <;> ring
  rw [smoothCurveSeries_coeff_of_approximation f (x * y) (P * Q) (n + 1)
    (by omega) hprod n (by omega), Polynomial.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hij' := Finset.mem_antidiagonal.mp hij
  rw [smoothCurveSeries_coeff_of_approximation f x P (n + 1) (by omega) hP
    ij.1 (by omega),
    smoothCurveSeries_coeff_of_approximation f y Q (n + 1) (by omega) hQ
      ij.2 (by omega)]

def smoothCurveSeriesAlgHom : A →ₐ[K] PowerSeries K :=
  { toFun := smoothCurveSeries f
    map_zero' := smoothCurveSeries_zero f
    map_one' := smoothCurveSeries_one f
    map_add' := smoothCurveSeries_add f
    map_mul' := smoothCurveSeries_mul f
    commutes' := fun a ↦ by
      ext n
      have h := smoothCurveSeries_coeff_of_approximation f (algebraMap K A a)
        (Polynomial.C a) (n + 1) (by omega) (by
          change smoothCurvePolynomialCoordinate f (algebraMap K (Polynomial K) a) -
            algebraMap K A a ∈ _
          rw [(smoothCurvePolynomialCoordinate f).commutes a]
          simp) n (by omega)
      simpa only [Polynomial.coeff_C, PowerSeries.algebraMap_apply,
        PowerSeries.coeff_C] using h }

theorem smoothCurvePolynomialCoordinate_X_mem_ker :
    smoothCurvePolynomialCoordinate f Polynomial.X ∈ RingHom.ker f.toRingHom := by
  change f (smoothCoordinateMap f 1 ((oneVariablePolynomialAlgEquiv K).symm Polynomial.X)) = 0
  rw [← AlgHom.comp_apply, comp_smoothCoordinateMap_eq_polynomialOriginAugmentation]
  change MvPolynomial.constantCoeff ((oneVariablePolynomialAlgEquiv K).symm Polynomial.X) = 0
  rw [← oneVariablePolynomialAlgEquiv_eval_zero]
  simp

theorem smoothCurveSeriesAlgHom_injective
    [IsNoetherianRing A] [IsDomain A] :
    Function.Injective (smoothCurveSeriesAlgHom f) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  have hm : RingHom.ker f.toRingHom ≠ ⊤ := by
    intro htop
    have h : (1 : A) ∈ RingHom.ker f.toRingHom := by rw [htop]; trivial
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using h)
  have hmem : x ∈ ⨅ n : ℕ, RingHom.ker f.toRingHom ^ n := by
    simp only [Submodule.mem_iInf]
    intro n
    let P := smoothCurvePolynomialApproximation f n x
    have hP : smoothCurvePolynomialCoordinate f P - x ∈
        RingHom.ker f.toRingHom ^ (n + 1 + 1) :=
      smoothCurvePolynomialApproximation_spec f n x
    have hcoeff : ∀ i < n + 1, P.coeff i = 0 := by
      intro i hi
      have h := smoothCurveSeries_coeff_of_approximation f x P (n + 1)
        (by omega) hP i hi
      change PowerSeries.coeff i (smoothCurveSeriesAlgHom f x) = _ at h
      simpa only [hx, map_zero] using h.symm
    obtain ⟨Q, hQ⟩ := Polynomial.X_pow_dvd_iff.mpr hcoeff
    have hmap : smoothCurvePolynomialCoordinate f P ∈
        RingHom.ker f.toRingHom ^ (n + 1) := by
      rw [hQ, map_mul, map_pow]
      exact Ideal.mul_mem_right _ _
        (Ideal.pow_mem_pow (smoothCurvePolynomialCoordinate_X_mem_ker f) (n + 1))
    have hxmem : x ∈ RingHom.ker f.toRingHom ^ (n + 1) := by
      have hdiff := Ideal.pow_le_pow_right (show n + 1 ≤ n + 1 + 1 by omega) hP
      simpa using (RingHom.ker f.toRingHom ^ (n + 1)).sub_mem hmap hdiff
    exact Ideal.pow_le_pow_right (by omega) hxmem
  have hsep : (⨅ n : ℕ, RingHom.ker f.toRingHom ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isDomain _ hm
  rw [hsep] at hmem
  exact hmem

end

end TranslatedDepthSeven
