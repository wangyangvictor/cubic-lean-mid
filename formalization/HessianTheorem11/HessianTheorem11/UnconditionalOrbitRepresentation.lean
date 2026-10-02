import HessianTheorem11.UnconditionalOrbitCoefficients
import HessianTheorem11.UnconditionalOrbitIdealFinite
import Mathlib.Algebra.MvPolynomial.Funext

/-! Invertible pullback on the actual finite-dimensional target ideal and
the equivariant evaluation map. The target zero locus is retained exactly. -/
noncomputable section
namespace HessianTheorem11.UnconditionalOrbitIdeal
open MvPolynomial PolynomialRestriction PolynomialWeightTransport ReducedRelative
variable {K : Type*} [Field K] {n d : ℕ}

theorem finiteCoefficientMatrix_mul (B C : Matrix (Fin n) (Fin n) K) :
    finiteCoefficientMatrix (d := d) B * finiteCoefficientMatrix C =
      finiteCoefficientMatrix (C * B) := by
  classical
  have h (x : DegreeIndex n d → K) :
      (finiteCoefficientMatrix B).mulVec ((finiteCoefficientMatrix C).mulVec x) =
        (finiteCoefficientMatrix (C*B)).mulVec x := by
    calc
      _ = coefficientVector (restrict B (restrict C (decode x))) := by
        rw [coefficientVector_restrict B _ (homogeneous_restrict C _ (decode_homogeneous x)),
          coefficientVector_restrict C _ (decode_homogeneous x),coefficientVector_decode]
      _ = _ := by
        rw [restrict_restrict,coefficientVector_restrict _ _ (decode_homogeneous x),
          coefficientVector_decode]
  ext i j
  have hh := congrFun (h (Pi.single j 1)) i
  simpa only [Matrix.mulVec_mulVec,Matrix.mulVec_single_one] using hh

@[simp] theorem finiteCoefficientMatrix_one :
    finiteCoefficientMatrix (K := K) (d := d) (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  classical
  ext i j
  change coeff i.val (restrict 1 (monomial j.val 1)) = _
  rw [restrict_one]
  by_cases hij : i = j
  · subst j
    simp
  · have hv : j.val ≠ i.val := fun h => hij (Subtype.ext h.symm)
    simp [coeff_monomial,hv,Matrix.one_apply,hij]

theorem restrict_restrict_finite [Infinite K] {σ : Type*} [Fintype σ]
    (B C : Matrix σ σ K) (P : MvPolynomial σ K) :
    restrict C (restrict B P) = restrict (B*C) P := by
  apply MvPolynomial.funext
  intro x
  simp only [eval_restrict,Matrix.mulVec_mulVec]

theorem restrict_one_finite [Infinite K] {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial σ K) : restrict (1 : Matrix σ σ K) P = P := by
  apply MvPolynomial.funext
  intro x
  simp only [eval_restrict,Matrix.one_mulVec]

def boundedPullbackEquiv [Infinite K] {σ : Type*} [Fintype σ] [DecidableEq σ]
    (B C : Matrix σ σ K) (hBC : B*C=1) (hCB : C*B=1)
    (S : Set (σ → K)) (N : ℕ)
    (hBS : ∀ x ∈ S, B.mulVec x ∈ S) (hCS : ∀ x ∈ S, C.mulVec x ∈ S) :
    boundedIdeal S N ≃ₗ[K] boundedIdeal S N where
  toLinearMap := boundedPullback B S N hBS
  invFun := boundedPullback C S N hCS
  left_inv P := by
    apply Subtype.ext
    change restrict C (restrict B P.val) = P.val
    rw [restrict_restrict_finite,hBC,restrict_one_finite]
  right_inv P := by
    apply Subtype.ext
    change restrict B (restrict C P.val) = P.val
    rw [restrict_restrict_finite,hCB,restrict_one_finite]

def targetPullback [Infinite K] (S : Set (MvPolynomial (Fin n) K))
    (hS : slInvariant S) (hhom : ∀ F ∈ S, F.IsHomogeneous d) (N : ℕ)
    (B : Matrix (Fin n) (Fin n) K) (hB : B.det=1) :
    boundedIdeal (finiteTarget (d := d) S) N ≃ₗ[K]
      boundedIdeal (finiteTarget (d := d) S) N := by
  have hunit : IsUnit B.det := hB ▸ isUnit_one
  have hBi : B⁻¹.det=1 := by rw [Matrix.det_nonsing_inv,hB,Ring.inverse_one]
  exact boundedPullbackEquiv (finiteCoefficientMatrix B) (finiteCoefficientMatrix B⁻¹)
    (by rw [finiteCoefficientMatrix_mul,Matrix.nonsing_inv_mul B hunit,finiteCoefficientMatrix_one])
    (by rw [finiteCoefficientMatrix_mul,Matrix.mul_nonsing_inv B hunit,finiteCoefficientMatrix_one])
    (finiteTarget S) N (finiteTarget_invariant S hS hhom B hB)
    (finiteTarget_invariant S hS hhom B⁻¹ hBi)

theorem targetPullback_mul [Infinite K] (S : Set (MvPolynomial (Fin n) K))
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (N : ℕ)
    (B C : Matrix (Fin n) (Fin n) K) (hB : B.det=1) (hC : C.det=1)
    (P : boundedIdeal (finiteTarget (d := d) S) N) :
    targetPullback S hS hhom N B hB (targetPullback S hS hhom N C hC P) =
      targetPullback S hS hhom N (B*C) (by rw [Matrix.det_mul,hB,hC,one_mul]) P := by
  apply Subtype.ext
  change restrict (finiteCoefficientMatrix B) (restrict (finiteCoefficientMatrix C) P.val) =
    restrict (finiteCoefficientMatrix (B*C)) P.val
  rw [restrict_restrict_finite,finiteCoefficientMatrix_mul]

theorem targetPullback_one [Infinite K] (S : Set (MvPolynomial (Fin n) K))
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (N : ℕ)
    (P : boundedIdeal (finiteTarget (d := d) S) N) :
    targetPullback S hS hhom N 1 (Matrix.det_one) P = P := by
  apply Subtype.ext
  change restrict (finiteCoefficientMatrix 1) P.val = P.val
  rw [finiteCoefficientMatrix_one,restrict_one_finite]

theorem targetEvaluation_equivariance [Infinite K] (S : Set (MvPolynomial (Fin n) K))
    (hS : slInvariant S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) (N : ℕ)
    (B : Matrix (Fin n) (Fin n) K) (hB : B.det=1)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d) :
    boundedEvaluation (finiteTarget (d := d) S) N (coefficientVector (restrict B F)) =
      (boundedEvaluation (finiteTarget (d := d) S) N (coefficientVector F)).comp
        (targetPullback S hS hhom N B hB).toLinearMap := by
  apply LinearMap.ext
  intro P
  rw [coefficientVector_restrict B F hF]
  exact (boundedEvaluation_pullback (finiteCoefficientMatrix B) (finiteTarget S) N
    (finiteTarget_invariant S hS hhom B hB) (coefficientVector F) P).symm

/-- Some actual finite-dimensional stable space of equations has evaluation
zero precisely on the closed target, for every degree-d form. -/
theorem exists_exact_target_evaluation (S : Set (MvPolynomial (Fin n) K))
    (hclosed : coefficientClosed S) (hhom : ∀ G ∈ S, G.IsHomogeneous d) :
    ∃ N : ℕ, ∀ F : MvPolynomial (Fin n) K, F.IsHomogeneous d →
      (boundedEvaluation (finiteTarget (d := d) S) N (coefficientVector F) = 0 ↔ F ∈ S) := by
  obtain ⟨N,hN⟩ := exists_boundedIdeal_generates (finiteTarget (d := d) S)
  refine ⟨N,?_⟩
  intro F hF
  rw [boundedEvaluation_eq_zero_iff _ N hN,finiteTarget_zeroLocus S hclosed hhom]
  constructor
  · rintro ⟨G,hG,hGF⟩
    have he := congrArg decode hGF
    rw [decode_coefficientVector G (hhom G hG),decode_coefficientVector F hF] at he
    exact he ▸ hG
  · intro hFS
    exact ⟨F,hFS,rfl⟩

end HessianTheorem11.UnconditionalOrbitIdeal
