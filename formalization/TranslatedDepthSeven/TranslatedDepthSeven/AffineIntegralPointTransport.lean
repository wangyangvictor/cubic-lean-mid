import TranslatedDepthSeven.AffinePolynomialChange
import TranslatedDepthSeven.CongruenceRescaling

/-!
# Integral points under an affine congruence rescaling

This file gives the exact point-level bridge used before a Pila estimate.
For a positive integer `r`, the integral vectors congruent to `x₀` modulo
`r` are equivalent to all integral vectors by `x = x₀ + r z`.  It also
proves, over `ℚ`, that polynomial vanishing is carried to vanishing of the
literal affine transform of the polynomial.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial

/-- The integral affine map `z ↦ x₀ + r z`. -/
def integralAffineMap {n : ℕ} (x₀ z : IntVector n) (r : ℕ) : IntVector n :=
  fun i ↦ x₀ i + r * z i

/-- The affine image is coordinatewise congruent to its base point. -/
theorem integralAffineMap_congruent {n r : ℕ} (x₀ z : IntVector n) :
    IntVectorCongruent r (integralAffineMap x₀ z r) x₀ := by
  intro i
  simp [integralAffineMap]

/-- For positive scale, the integral affine map is injective. -/
theorem integralAffineMap_injective {n r : ℕ} (hr : 0 < r) (x₀ : IntVector n) :
    Function.Injective (fun z ↦ integralAffineMap x₀ z r) := by
  intro z z' h
  apply intVector_rescaling_unique hr
      (x := integralAffineMap x₀ z r) (x₀ := x₀)
  · intro i
    rfl
  · intro i
    exact congrFun h i

/-- Choose the unique displacement of a point in the congruence class. -/
def congruenceDisplacement {n r : ℕ} (x₀ : IntVector n)
    (x : {x : IntVector n // IntVectorCongruent r x x₀}) : IntVector n :=
  Classical.choose (exists_intVector_rescaling x.property)

theorem congruenceDisplacement_spec {n r : ℕ} (x₀ : IntVector n)
    (x : {x : IntVector n // IntVectorCongruent r x x₀}) (i : Fin n) :
    x.1 i = x₀ i + r * congruenceDisplacement x₀ x i :=
  Classical.choose_spec (exists_intVector_rescaling x.property) i

/-- If both the base point and a congruent point lie in one translated box,
the chosen displacement lies in the rescaled box. -/
theorem congruenceDisplacement_coordinate_bound {n r : ℕ} (hr : 0 < r)
    (x₀ : IntVector n)
    (x : {x : IntVector n // IntVectorCongruent r x x₀})
    {center : RealVector n} {R : ℝ}
    (hx : ∀ i, |(x.1 i : ℝ) - center i| ≤ R)
    (hx₀ : ∀ i, |(x₀ i : ℝ) - center i| ≤ R) (i : Fin n) :
    |(congruenceDisplacement x₀ x i : ℝ)| ≤ 2 * R / r :=
  intVector_rescaling_coordinate_bound hr hx hx₀
    (congruenceDisplacement_spec x₀ x) i

/-- The congruence class and the rescaled integral lattice are exactly
equivalent. -/
def congruenceDisplacementEquiv {n r : ℕ} (hr : 0 < r) (x₀ : IntVector n) :
    {x : IntVector n // IntVectorCongruent r x x₀} ≃ IntVector n where
  toFun := congruenceDisplacement x₀
  invFun z := ⟨integralAffineMap x₀ z r, integralAffineMap_congruent x₀ z⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact (congruenceDisplacement_spec x₀ x i).symm
  right_inv z := by
    apply intVector_rescaling_unique hr
        (x := integralAffineMap x₀ z r) (x₀ := x₀)
    · intro i
      exact congruenceDisplacement_spec x₀
        (⟨integralAffineMap x₀ z r, integralAffineMap_congruent x₀ z⟩) i
    · intro i
      rfl

/-- A finite subset of one congruence class has exactly the same cardinality
after rescaling. -/
theorem card_image_congruenceDisplacementEquiv {n r : ℕ} (hr : 0 < r)
    (x₀ : IntVector n)
    (A : Finset {x : IntVector n // IntVectorCongruent r x x₀}) :
    (A.image (congruenceDisplacementEquiv hr x₀)).card = A.card := by
  exact Finset.card_image_iff.mpr
    (Set.injOn_of_injective (congruenceDisplacementEquiv hr x₀).injective)

/-- Integral substitution `X i ↦ x₀ i + r X i`.  In contrast with the
rational transform below, this definition does not use an inverse and hence
retains integral coefficients literally. -/
def integralAffineTransform {n : ℕ} (x₀ : IntVector n) (r : ℕ)
    (f : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin n) ℤ :=
  (aeval fun i ↦ C (x₀ i) + C (r : ℤ) * X i) f

/-- Exact evaluation identity for the integral transform. -/
theorem aeval_integralAffineTransform {n : ℕ} (x₀ z : IntVector n) (r : ℕ)
    (f : MvPolynomial (Fin n) ℤ) :
    aeval z (integralAffineTransform x₀ r f) =
      aeval (integralAffineMap x₀ z r) f := by
  change (aeval z).comp (aeval fun i ↦ C (x₀ i) + C (r : ℤ) * X i) f = _
  congr 1
  ext i
  simp [integralAffineMap]

/-- The polynomial obtained over `ℚ` by the substitution `x = x₀ + r z`. -/
def rationalAffineTransform {n r : ℕ} (hr : 0 < r) (x₀ : IntVector n)
    (f : MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin n) ℚ :=
  affinePolynomialChangeAlgEquiv (fun i ↦ (x₀ i : ℚ)) (r : ℚ)
    (by exact_mod_cast hr.ne') f

/-- Extending coefficients from `ℤ` to `ℚ` commutes with the literal
integral affine substitution.  Thus the integral and rational transforms
above are the same polynomial after base change. -/
theorem map_integralAffineTransform {n r : ℕ} (hr : 0 < r)
    (x₀ : IntVector n) (f : MvPolynomial (Fin n) ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ) (integralAffineTransform x₀ r f) =
      rationalAffineTransform hr x₀
        (MvPolynomial.map (Int.castRingHom ℚ) f) := by
  let lhs : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℚ :=
    (MvPolynomial.map (Int.castRingHom ℚ)).comp
      (aeval fun i ↦ C (x₀ i) + C (r : ℤ) * X i).toRingHom
  let rhs : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℚ :=
    (affinePolynomialChangeAlgEquiv (fun i ↦ (x₀ i : ℚ)) (r : ℚ)
      (by exact_mod_cast hr.ne')).toRingHom.comp
        (MvPolynomial.map (Int.castRingHom ℚ))
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, rhs]
    · intro i
      simp [lhs, rhs]
  change lhs f = rhs f
  exact RingHom.congr_fun hhom f

/-- The rational affine transform preserves total degree exactly. -/
theorem totalDegree_rationalAffineTransform {n r : ℕ} (hr : 0 < r)
    (x₀ : IntVector n) (f : MvPolynomial (Fin n) ℚ) :
    (rationalAffineTransform hr x₀ f).totalDegree = f.totalDegree := by
  exact totalDegree_affinePolynomialChange _ _ _ f

/-- The literal integral substitution preserves total degree whenever its
scale is positive.  The proof uses the preceding base-change identity and
the injectivity of `ℤ → ℚ`; hence no cancellation of the leading form is
silently assumed. -/
theorem totalDegree_integralAffineTransform {n r : ℕ} (hr : 0 < r)
    (x₀ : IntVector n) (f : MvPolynomial (Fin n) ℤ) :
    (integralAffineTransform x₀ r f).totalDegree = f.totalDegree := by
  have hmapDegree (g : MvPolynomial (Fin n) ℤ) :
      (MvPolynomial.map (Int.castRingHom ℚ) g).totalDegree = g.totalDegree := by
    unfold MvPolynomial.totalDegree
    rw [MvPolynomial.support_map_of_injective g Int.cast_injective]
  calc
    (integralAffineTransform x₀ r f).totalDegree =
        (MvPolynomial.map (Int.castRingHom ℚ)
          (integralAffineTransform x₀ r f)).totalDegree :=
      (hmapDegree _).symm
    _ = (rationalAffineTransform hr x₀
          (MvPolynomial.map (Int.castRingHom ℚ) f)).totalDegree := by
      rw [map_integralAffineTransform hr x₀ f]
    _ = (MvPolynomial.map (Int.castRingHom ℚ) f).totalDegree :=
      totalDegree_rationalAffineTransform hr x₀ _
    _ = f.totalDegree := hmapDegree f

/-- Exact evaluation identity for the integral affine rescaling. -/
theorem aeval_rationalAffineTransform {n r : ℕ} (hr : 0 < r)
    (x₀ z : IntVector n) (f : MvPolynomial (Fin n) ℚ) :
    aeval (fun i ↦ (z i : ℚ)) (rationalAffineTransform hr x₀ f) =
      aeval (fun i ↦ (integralAffineMap x₀ z r i : ℚ)) f := by
  rw [rationalAffineTransform, aeval_affinePolynomialChange]
  apply congrArg (fun y : Fin n → ℚ ↦ aeval y f)
  funext i
  simp [integralAffineMap]

/-- Polynomial vanishing is transported exactly by `x = x₀ + r z`. -/
theorem aeval_rationalAffineTransform_eq_zero_iff {n r : ℕ} (hr : 0 < r)
    (x₀ z : IntVector n) (f : MvPolynomial (Fin n) ℚ) :
    aeval (fun i ↦ (z i : ℚ)) (rationalAffineTransform hr x₀ f) = 0 ↔
      aeval (fun i ↦ (integralAffineMap x₀ z r i : ℚ)) f = 0 := by
  rw [aeval_rationalAffineTransform]

/-- The displacement of a point in the congruence class satisfies the exact
polynomial-vanishing equivalence. -/
theorem aeval_congruenceDisplacement_eq_zero_iff {n r : ℕ} (hr : 0 < r)
    (x₀ : IntVector n)
    (x : {x : IntVector n // IntVectorCongruent r x x₀})
    (f : MvPolynomial (Fin n) ℚ) :
    aeval (fun i ↦ (congruenceDisplacement x₀ x i : ℚ))
        (rationalAffineTransform hr x₀ f) = 0 ↔
      aeval (fun i ↦ (x.1 i : ℚ)) f = 0 := by
  rw [aeval_rationalAffineTransform]
  have hpoints :
      (fun i ↦ (integralAffineMap x₀ (congruenceDisplacement x₀ x) r i : ℚ)) =
        (fun i ↦ (x.1 i : ℚ)) := by
    funext i
    rw [congruenceDisplacement_spec]
    simp [integralAffineMap]
  rw [hpoints]

/-- The preceding equivalence holds simultaneously for a literal finite
family of equations. -/
theorem all_aeval_congruenceDisplacement_eq_zero_iff {n r : ℕ} (hr : 0 < r)
    (x₀ : IntVector n)
    (x : {x : IntVector n // IntVectorCongruent r x x₀})
    (equations : Finset (MvPolynomial (Fin n) ℚ)) :
    (∀ f ∈ equations,
        aeval (fun i ↦ (congruenceDisplacement x₀ x i : ℚ))
          (rationalAffineTransform hr x₀ f) = 0) ↔
      (∀ f ∈ equations, aeval (fun i ↦ (x.1 i : ℚ)) f = 0) := by
  constructor <;> intro h f hf
  · exact (aeval_congruenceDisplacement_eq_zero_iff hr x₀ x f).mp (h f hf)
  · exact (aeval_congruenceDisplacement_eq_zero_iff hr x₀ x f).mpr (h f hf)

end

end TranslatedDepthSeven
