import HessianTheorem11.PolynomialRestriction
import HessianTheorem11.QuadricGram

/-! Polynomial identities for a linear matrix pencil, including cancellation
of a nonzero scalar factor in its cyclic moments. -/
noncomputable section
namespace HessianTheorem11.PolynomialMoments
open Matrix MvPolynomial
variable {K R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]

def moment (B M : Matrix ι ι R) (v : ι → R) (j : ℕ) : R :=
  dotProduct v ((B * M^j).mulVec v)

theorem moment_map (φ : R →+* S) (B M : Matrix ι ι R) (v : ι → R) (j : ℕ) :
    φ (moment B M v j) = moment (B.map φ) (M.map φ) (fun i => φ (v i)) j := by
  have hh : (B * M^j).map φ = B.map φ * (M.map φ)^j := by
    rw [Matrix.map_mul,Matrix.map_pow]
  simp only [moment,dotProduct,mulVec,map_sum,map_mul]
  change ∑ i, φ (v i) * ∑ k, ((B*M^j).map φ) i k * φ (v k) = _
  rw [hh]

theorem moment_smul (B M : Matrix ι ι R) (v : ι → R) (c : R) (j : ℕ) :
    moment B M (c • v) j = c^2 * moment B M v j := by
  simp only [moment, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_smul]
  ring

variable [Field K] [Infinite K] {n : ℕ}

def matrixPencil (M : (Fin n → K) →ₗ[K] Matrix ι ι K) :
    Matrix ι ι (MvPolynomial (Fin n) K) :=
  ∑ i, (X i : MvPolynomial (Fin n) K) • (M (Pi.basisFun K (Fin n) i)).map (C : K →+* MvPolynomial (Fin n) K)

def linearPolynomial (l : (Fin n → K) →ₗ[K] K) : MvPolynomial (Fin n) K :=
  ∑ i, C (l (Pi.basisFun K (Fin n) i)) * X i

theorem matrixPencil_eval (M : (Fin n → K) →ₗ[K] Matrix ι ι K) (a : Fin n → K) :
    (matrixPencil M).map (eval a) = M a := by
  have ha := (Pi.basisFun K (Fin n)).sum_repr a
  simp only [Pi.basisFun_repr] at ha
  conv_rhs => rw [← ha,map_sum]
  ext i j
  simp [matrixPencil, Matrix.sum_apply, map_smul, Matrix.smul_apply]

theorem linearPolynomial_eval (l : (Fin n → K) →ₗ[K] K) (a : Fin n → K) :
    eval a (linearPolynomial l) = l a := by
  have ha := (Pi.basisFun K (Fin n)).sum_repr a
  simp only [Pi.basisFun_repr] at ha
  conv_rhs => rw [← ha,map_sum]
  simp [linearPolynomial,mul_comm]

theorem linearPolynomial_ne_zero (l : (Fin n → K) →ₗ[K] K)
    (h : ∃ a, l a ≠ 0) : linearPolynomial l ≠ 0 := by
  obtain ⟨a,ha⟩ := h
  intro hz
  apply ha
  rw [← linearPolynomial_eval, hz, map_zero]

/-- Vanishing on the complement of one nonzero linear equation already
forces every fixed-vector moment of the pencil to vanish everywhere. -/
theorem cancel_linear_factor (B : Matrix ι ι K)
    (M : (Fin n → K) →ₗ[K] Matrix ι ι K) (v : ι → K)
    (l : (Fin n → K) →ₗ[K] K) (hl : ∃ a, l a ≠ 0)
    (hm : ∀ a (j : ℕ), moment B (M a) (l a • v) j = 0) :
    ∀ a (j : ℕ), moment B (M a) v j = 0 := by
  intro a j
  let P := moment (B.map C) (matrixPencil M) (fun i => C (v i)) j
  have hPe (x : Fin n → K) : eval x P = moment B (M x) v j := by
    dsimp only [P]
    rw [moment_map,matrixPencil_eval]
    have hb : (B.map (C : K →+* MvPolynomial (Fin n) K)).map (eval x) = B := by ext i k; simp
    rw [hb]
    simp only [eval_C]
  have hp : (linearPolynomial l)^2 * P = 0 := by
    apply MvPolynomial.funext
    intro x
    simp only [map_mul,map_pow,map_zero,linearPolynomial_eval,hPe]
    simpa only [moment_smul] using hm x j
  have hP : P = 0 := (mul_eq_zero.mp hp).resolve_left
    (pow_ne_zero _ (linearPolynomial_ne_zero l hl))
  rw [← hPe,hP,map_zero]

end HessianTheorem11.PolynomialMoments
