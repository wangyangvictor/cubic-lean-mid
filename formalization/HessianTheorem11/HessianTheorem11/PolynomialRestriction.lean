import HessianTheorem11.Geometry

/-! Formal polynomial differentiation under linear restriction. -/

noncomputable section

namespace HessianTheorem11.PolynomialRestriction

open MvPolynomial
open scoped BigOperators

theorem pderiv_aeval
    {K m n : Type*} [CommRing K] [Fintype n]
    (g : n → MvPolynomial m K) (p : MvPolynomial n K) (j : m) :
    pderiv j (aeval g p) =
      ∑ i, aeval g (pderiv i p) * pderiv j (g i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, aeval_X,
        map_add, hp]
      simp only [add_mul, Finset.sum_add_distrib]
      simp only [pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero,
        mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      simp only [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The coordinate linear forms associated to a rectangular matrix. -/
def linearForms {K m n : Type*} [CommRing K] [Fintype m]
    (B : Matrix n m K) : n → MvPolynomial m K :=
  fun i => ∑ j, C (B i j) * X j

/-- Polynomial restriction along a linear map. -/
def restrict {K m n : Type*} [CommRing K] [Fintype m]
    (B : Matrix n m K) (p : MvPolynomial n K) : MvPolynomial m K :=
  aeval (linearForms B) p

@[simp] theorem pderiv_linearForms
    {K m n : Type*} [CommRing K] [Fintype m]
    (B : Matrix n m K) (i : n) (j : m) :
    pderiv j (linearForms B i) = C (B i j) := by
  classical
  simp [linearForms, Derivation.leibniz, smul_eq_mul, Pi.single_apply,
    mul_ite]

@[simp] theorem eval_linearForms
    {K m n : Type*} [CommRing K] [Fintype m]
    (B : Matrix n m K) (z : m → K) (i : n) :
    eval z (linearForms B i) = B.mulVec z i := by
  simp [linearForms, Matrix.mulVec, dotProduct]

@[simp] theorem eval_restrict
    {K m n : Type*} [CommRing K] [Fintype m]
    (B : Matrix n m K) (p : MvPolynomial n K) (z : m → K) :
    eval z (restrict B p) = eval (B.mulVec z) p := by
  change aeval z (aeval (linearForms B) p) = aeval (B.mulVec z) p
  rw [MvPolynomial.comp_aeval_apply]
  have hforms : (fun i => aeval z (linearForms B i)) = B.mulVec z :=
    funext (eval_linearForms B z)
  rw [hforms]

theorem pderiv_restrict
    {K m n : Type*} [CommRing K] [Fintype m] [Fintype n]
    (B : Matrix n m K) (p : MvPolynomial n K) (j : m) :
    pderiv j (restrict B p) = ∑ i, restrict B (pderiv i p) * C (B i j) := by
  simpa only [restrict, pderiv_linearForms] using pderiv_aeval (linearForms B) p j

theorem hessian_restrict
    {K : Type*} [CommRing K] {m n : ℕ}
    (B : Matrix (Fin n) (Fin m) K) (p : MvPolynomial (Fin n) K)
    (z : Fin m → K) :
    hessian (restrict B p) z = B.transpose * hessian p (B.mulVec z) * B := by
  classical
  ext i j
  simp only [hessian, hessianPolynomial, pderiv_restrict, map_sum,
    Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, zero_add,
    map_mul, eval_C, eval_restrict, Matrix.mul_apply, Matrix.transpose_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem homogeneous_linearForms
    {K m n : Type*} [CommRing K] [Fintype m]
    (B : Matrix n m K) (i : n) : (linearForms B i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j hj
  exact isHomogeneous_C_mul_X (B i j) j

theorem homogeneous_restrict
    {K m n : Type*} [CommRing K] [Fintype m]
    (B : Matrix n m K) (p : MvPolynomial n K) {d : ℕ}
    (hp : p.IsHomogeneous d) : (restrict B p).IsHomogeneous d := by
  simpa only [one_mul] using hp.aeval (linearForms B) (homogeneous_linearForms B)

theorem anisotropic_restrict
    {m n : ℕ} (B : Matrix (Fin n) (Fin m) ℚ) (p : RationalPolynomial n)
    (hp : Anisotropic p) (hB : Function.Injective B.mulVec) :
    Anisotropic (restrict B p) := by
  intro z hz
  apply hB
  rw [Matrix.mulVec_zero]
  apply hp
  rwa [eval_restrict] at hz

/-- An actual injective rational restriction packaged as an anisotropic cubic. -/
def restrictedCubic
    {m n : ℕ} (B : Matrix (Fin n) (Fin m) ℚ) (F : AnisotropicCubic n)
    (hB : Function.Injective B.mulVec) : AnisotropicCubic m where
  polynomial := restrict B F.polynomial
  homogeneous := homogeneous_restrict B F.polynomial F.homogeneous
  anisotropic := anisotropic_restrict B F.polynomial F.anisotropic hB

theorem map_restrict
    {K L m n : Type*} [CommRing K] [CommRing L] [Fintype m]
    (f : K →+* L) (B : Matrix n m K) (p : MvPolynomial n K) :
    map f (restrict B p) = restrict (B.map f) (map f p) := by
  change map f (eval₂ C (linearForms B) p) =
    eval₂ C (linearForms (B.map f)) (map f p)
  rw [MvPolynomial.map_eval₂]
  congr 1
  funext i
  simp [linearForms, Matrix.map_apply]

/-- The supremum of on-cubic full Hessian ranks cannot decrease when a
linear restriction is replaced by its ambient polynomial. -/
theorem genericHessianRank_restrict_le
    {m n : ℕ} (B : Matrix (Fin n) (Fin m) ℚ) (p : RationalPolynomial n) :
    genericHessianRank (restrict B p) ≤ genericHessianRank p := by
  apply csSup_le'
  rintro r ⟨z, hz, rfl⟩
  have hz' : (B.map (algebraMap ℚ GeometricField)).mulVec z ∈ cubicLocus p := by
    simpa only [cubicLocus, Set.mem_setOf_eq, geometricPolynomial,
      map_restrict, eval_restrict] using hz
  rw [geometricPolynomial, map_restrict, hessian_restrict]
  exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans
    (rank_le_genericHessianRank p hz')

/-- Corollary 28.1's rank transfer for any displayed injective rational
ten-dimensional restriction. The bespoke ten-variable theorem is stated
explicitly as the premise that remains to be proved. -/
theorem rank_ten_of_ten_variable_theorem
    (hten : ∀ F : AnisotropicCubic 10, 10 ≤ genericHessianRank F.polynomial)
    {n : ℕ} (F : AnisotropicCubic n) (B : Matrix (Fin n) (Fin 10) ℚ)
    (hB : Function.Injective B.mulVec) : 10 ≤ genericHessianRank F.polynomial :=
  (hten (restrictedCubic B F hB)).trans (genericHessianRank_restrict_le B F.polynomial)

/-- The inclusion of the first `m` coordinate directions in `n` variables. -/
def coordinateInclusion {K : Type*} [Zero K] [One K] {m n : ℕ} (_h : m ≤ n) :
    Matrix (Fin n) (Fin m) K :=
  fun i j => if i.val = j.val then 1 else 0

theorem coordinateInclusion_injective
    {K : Type*} [CommRing K] {m n : ℕ} (h : m ≤ n) :
    Function.Injective (coordinateInclusion (K := K) h).mulVec := by
  classical
  intro u v huv
  funext j
  let i : Fin n := ⟨j.val, lt_of_lt_of_le j.isLt h⟩
  have hrow (k : Fin m) : coordinateInclusion (K := K) h i k =
      if k = j then 1 else 0 := by
    simp [coordinateInclusion, i, Fin.ext_iff, eq_comm]
  have heq := congrFun huv i
  simpa [Matrix.mulVec, dotProduct, hrow] using heq

/-- The entire restriction step, with no unspecified matrix or chain-rule
premise: any ten-variable theorem propagates to every larger dimension. -/
theorem rank_ten_in_all_larger_dimensions
    (hten : ∀ F : AnisotropicCubic 10, 10 ≤ genericHessianRank F.polynomial)
    {n : ℕ} (hn : 10 ≤ n) (F : AnisotropicCubic n) :
    10 ≤ genericHessianRank F.polynomial :=
  rank_ten_of_ten_variable_theorem hten F (coordinateInclusion hn)
    (coordinateInclusion_injective hn)

end HessianTheorem11.PolynomialRestriction
