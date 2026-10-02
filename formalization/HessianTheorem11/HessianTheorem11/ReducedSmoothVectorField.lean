import HessianTheorem11.ReducedTangentRank
import HessianTheorem11.KernelAnnihilatorProjector

/-! A tangent vector at an actual smooth point extends to a polynomial
derivation preserving the reduced vanishing ideal. A maximal Jacobian minor
and its adjugate provide the vector field explicitly. -/

noncomputable section
namespace HessianTheorem11.ReducedSmoothVectorField
open MvPolynomial Module ReducedTangentRank KernelAnnihilatorProjector
set_option maxHeartbeats 1000000

def vectorFieldDerivation {n : ℕ} (W : Fin n → GeometricPolynomial n) :
    Derivation GeometricField (GeometricPolynomial n) (GeometricPolynomial n) :=
  ∑ i, W i • pderiv i

@[simp] theorem vectorFieldDerivation_apply {n : ℕ}
    (W : Fin n → GeometricPolynomial n) (p : GeometricPolynomial n) :
    vectorFieldDerivation W p = ∑ i, W i * pderiv i p := by
  classical
  have hs (s : Finset (Fin n)) :
      (∑ i ∈ s, W i • pderiv i) p = ∑ i ∈ s, W i * pderiv i p := by
    induction s using Finset.induction_on with
    | empty => simp [Derivation.zero_apply]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Derivation.add_apply, Derivation.smul_apply,
        smul_eq_mul, ih]
  exact hs Finset.univ

@[simp] theorem vectorFieldDerivation_X {n : ℕ}
    (W : Fin n → GeometricPolynomial n) (i : Fin n) :
    vectorFieldDerivation W (X i) = W i := by
  simp [vectorFieldDerivation_apply, pderiv_X, Pi.single_apply]

theorem eval_vectorFieldDerivation {n : ℕ}
    (W : Fin n → GeometricPolynomial n) (p : GeometricPolynomial n)
    (y : GeometricPoint n) :
    eval y (vectorFieldDerivation W p) =
      polynomialDifferential p y (fun i => eval y (W i)) := by
  simp only [vectorFieldDerivation_apply, map_sum, map_mul, polynomialDifferential_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- No local smoothness package is assumed: the only geometric input is
the retained general generic-rank theorem. -/
theorem exists_tangent_derivation (GR : GenericRankOpenInput) {n : ℕ}
    (Z : Set (GeometricPoint n)) (hZ : AlgebraicallyClosedSet Z)
    (hirred : GeometricallyIrreducible Z)
    (x : GeometricPoint n) (hx : x ∈ Z)
    (hsmooth : affineDimension Z =
      (finrank GeometricField (affineTangentSpace Z x) : Dimension))
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z x) :
    ∃ D : Derivation GeometricField (GeometricPolynomial n) (GeometricPolynomial n),
      (∀ p ∈ vanishingIdeal GeometricField Z, D p ∈ vanishingIdeal GeometricField Z) ∧
      ∀ i, eval x (D (X i)) = v i := by
  classical
  obtain ⟨c, f, _, hf⟩ := exists_tangent_equations Z
  let J := jacobian f
  obtain ⟨G⟩ := GR.choose Z hZ hirred (fun _ : Fin 0 => (0 : GeometricPolynomial n))
    (0 : GeometricPoint n →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
  have hmax (y : GeometricPoint n) (hy : y ∈ Z) :
      (evaluatedMatrix J y).rank ≤ (evaluatedMatrix J x).rank := by
    have ht := tangent_dimension_lower_bound G y hy
    rw [hsmooth] at ht
    have ht' : finrank GeometricField (affineTangentSpace Z x) ≤
        finrank GeometricField (affineTangentSpace Z y) := by exact_mod_cast ht
    have h1 := rank_add_ker (evaluatedMatrix J x)
    have h2 := rank_add_ker (evaluatedMatrix J y)
    rw [show J = jacobian f from rfl, evaluated_jacobian, ← hf x hx] at h1
    rw [show J = jacobian f from rfl, evaluated_jacobian, ← hf y hy] at h2
    change (evaluatedMatrix (jacobian f) y).rank ≤ (evaluatedMatrix (jacobian f) x).rank
    omega
  obtain ⟨rows, cols, hdet⟩ := MatrixRankMinors.exists_rank_minor (evaluatedMatrix J x)
  let q : GeometricPolynomial n := (J.submatrix rows cols).det
  have hqx : eval x q ≠ 0 := by simpa only [q, RingHom.map_det] using hdet
  let Q := projector J rows cols
  let w : GeometricPoint n := (eval x q)⁻¹ • v
  let W : Fin n → GeometricPolynomial n := fun i => ∑ j, Q i j * C (w j)
  have hW (y : GeometricPoint n) :
      (fun i => eval y (W i)) = (projector (evaluatedMatrix J y) rows cols).mulVec w := by
    have he := projector_map (eval y) J rows cols
    funext i
    simp only [W, map_sum, map_mul, eval_C, Matrix.mulVec, dotProduct]
    congr 1
    funext j
    exact congrArg (fun N => N i j * w j) he
  have hWtangent (y : GeometricPoint n) (hy : y ∈ Z) (hqy : eval y q ≠ 0) :
      (fun i => eval y (W i)) ∈ affineTangentSpace Z y := by
    rw [hf y hy, ← evaluated_jacobian, ← show J = jacobian f from rfl, hW]
    apply projector_mem_ker _ rows cols _ (hmax y hy) w
    simpa only [q, RingHom.map_det] using hqy
  refine ⟨vectorFieldDerivation W, ?_, ?_⟩
  · intro p hp
    have hprod : q * vectorFieldDerivation W p ∈ vanishingIdeal GeometricField Z := by
      intro y hy
      change eval y (q * vectorFieldDerivation W p) = 0
      rw [map_mul]
      by_cases hqy : eval y q = 0
      · rw [hqy, zero_mul]
      · rw [eval_vectorFieldDerivation,
          mem_affineTangentSpace.mp (hWtangent y hy hqy) p hp, mul_zero]
    exact (hirred.mem_or_mem hprod).resolve_left (fun hq => hqx (hq x hx))
  · intro i
    rw [vectorFieldDerivation_X]
    have hvker : v ∈ LinearMap.ker (evaluatedMatrix J x).mulVecLin := by
      rwa [show J = jacobian f from rfl, evaluated_jacobian, ← hf x hx]
    have hw := hW x
    rw [show w = (eval x q)⁻¹ • v from rfl, Matrix.mulVec_smul,
      projector_on_ker _ rows cols v hvker] at hw
    have hqdet : ((evaluatedMatrix J x).submatrix rows cols).det = eval x q := by
      exact (RingHom.map_det (eval x) (J.submatrix rows cols)).symm
    rw [hqdet, smul_smul, inv_mul_cancel₀ hqx, one_smul] at hw
    exact congrFun hw i

end HessianTheorem11.ReducedSmoothVectorField
