import HessianTheorem11.SaturatedSchur
import HessianTheorem11.PencilSchurVanishing

/-! The exact formal resolvent of the saturated incidence pencil. -/
noncomputable section
namespace HessianTheorem11.SaturatedResolvent
open Matrix PencilSchurVanishing

variable {K α β γ : Type*} [Field K] [Fintype α] [Fintype β] [Fintype γ]

/-- The invertible constant Gram matrix in the order middle, isotropic,
dual isotropic. -/
def initial [DecidableEq β] (B : Matrix α α K) :
    Matrix (α ⊕ (β ⊕ β)) (α ⊕ (β ⊕ β)) K :=
  Matrix.fromBlocks B 0 0 (Matrix.fromBlocks 0 1 1 0)

/-- The radical-to-complement block is supported precisely on the dual space. -/
def cross {R : Type*} [Zero R] (P : Matrix γ β R) : Matrix γ (α ⊕ (β ⊕ β)) R :=
  Matrix.fromCols 0 (Matrix.fromCols 0 P)

theorem initial_mul [DecidableEq α] [DecidableEq β]
    (B R : Matrix α α K) (h : B * R = 1) : initial B * initial (β := β) R = 1 := by
  simp [initial, Matrix.fromBlocks_multiply, h, ← Matrix.fromBlocks_one]

theorem initial_isUnit_det [DecidableEq α] [DecidableEq β]
    (B : Matrix α α K) (hB : B.det ≠ 0) : IsUnit (initial (β := β) B).det :=
  Matrix.isUnit_det_of_right_inverse
    (initial_mul B B⁻¹ (Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB)))

theorem cross_product {R : Type*} [CommRing R]
    (P : Matrix γ β R)
    (J : Matrix (α ⊕ (β ⊕ β)) (α ⊕ (β ⊕ β)) R) :
    cross (α := α) P * J * (cross P).transpose =
      P * J.submatrix (fun i => Sum.inr (Sum.inr i))
        (fun i => Sum.inr (Sum.inr i)) * P.transpose := by
  ext i j
  simp [cross, Matrix.mul_apply, Fintype.sum_sum_type]

theorem cross_map {R : Type*} [CommRing R] (φ : K →+* R) (P : Matrix γ β K) :
    (cross (α := α) P).map φ = cross (P.map φ) := by
  ext i j
  rcases j with j | (j | j) <;> simp [cross]

theorem cross_schur_cancel [DecidableEq β]
    (P : Matrix γ β K) (L : Matrix β γ K) (hLP : L * P = 1)
    (J : Matrix (α ⊕ (β ⊕ β)) (α ⊕ (β ⊕ β)) (PowerSeries K))
    (h : seriesPencil (0 : Matrix γ γ K) 0 -
      seriesPencil 0 (cross P) * J * seriesPencil 0 (cross P).transpose = 0) :
    J.submatrix (fun i => Sum.inr (Sum.inr i))
      (fun i => Sum.inr (Sum.inr i)) = 0 := by
  have hz : cross (α := α) (P.map PowerSeries.C) * J * (cross (α := α) (P.map PowerSeries.C)).transpose = 0 := by
    simpa [seriesPencil, Matrix.map_zero, Matrix.transpose_map, cross_map,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, PowerSeries.X_ne_zero] using h
  rw [cross_product] at hz
  apply SaturatedSchur.cancel_outer_of_left_inverse (P.map PowerSeries.C)
    (L.map PowerSeries.C) _ _ hz
  simpa [Matrix.map_mul, Matrix.map_one]
    using congrArg (fun M : Matrix β β K => M.map PowerSeries.C) hLP

/-- Taking the first coefficient and cancelling the formal parameter gives
both asserted identities; this does not truncate the inverse series. -/
theorem cancel_formal_parameter
    (C : Matrix β β K) (S : Matrix β β (PowerSeries K))
    (h : (PowerSeries.X : PowerSeries K) • C.map PowerSeries.C - ((PowerSeries.X : PowerSeries K) ^ 2) • S = 0) :
    C = 0 ∧ S = 0 := by
  have he (i j : β) : PowerSeries.C (C i j) = PowerSeries.X * S i j := by
    apply mul_left_cancel₀ PowerSeries.X_ne_zero
    have hh := congrFun (congrFun h i) j
    change PowerSeries.X * PowerSeries.C (C i j) - PowerSeries.X^2 * S i j = 0 at hh
    rw [← sub_eq_zero]
    convert hh using 1 <;> ring
  have hC : C = 0 := by
    ext i j
    have hh := congrArg PowerSeries.constantCoeff (he i j)
    simpa using hh
  refine ⟨hC, ?_⟩
  apply Matrix.ext
  intro i j
  have hh := he i j
  rw [hC] at hh
  have hh' : PowerSeries.X * S i j = 0 := by simpa using hh.symm
  exact (mul_eq_zero.mp hh').resolve_left PowerSeries.X_ne_zero

/-- The exact middle-block resolvent follows from a vanishing inverse dual
block. The first variation may have arbitrary other blocks. -/
theorem resolvent_of_inverse_final_zero [DecidableEq α] [DecidableEq β]
    (B₀ : Matrix α α K) (hB₀ : B₀.det ≠ 0)
    (G₁ : Matrix (α ⊕ (β ⊕ β)) (α ⊕ (β ⊕ β)) K)
    (J : Matrix (α ⊕ (β ⊕ β)) (α ⊕ (β ⊕ β)) (PowerSeries K))
    (hGJ : seriesPencil (initial B₀) G₁ * J = 1)
    (hDD : J.submatrix (fun i => Sum.inr (Sum.inr i))
      (fun i => Sum.inr (Sum.inr i)) = 0) :
    G₁.submatrix (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inl i)) = 0 ∧
    (G₁.submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl).map PowerSeries.C *
      (seriesPencil B₀ (G₁.submatrix Sum.inl Sum.inl))⁻¹ *
      (G₁.submatrix Sum.inl (fun i => Sum.inr (Sum.inl i))).map PowerSeries.C = 0 := by
  let B := seriesPencil B₀ (G₁.submatrix Sum.inl Sum.inl)
  let G := seriesPencil (initial B₀) G₁
  have hB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B
    (seriesPencil_isUnit_det _ _ (isUnit_iff_ne_zero.mpr hB₀))
  have hblock : Matrix.fromBlocks B
      (Matrix.fromCols (G.submatrix Sum.inl (fun i => Sum.inr (Sum.inl i)))
        (G.submatrix Sum.inl (fun i => Sum.inr (Sum.inr i))))
      (Matrix.fromRows (G.submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl)
        (G.submatrix (fun i => Sum.inr (Sum.inr i)) Sum.inl))
      (Matrix.fromBlocks
        (G.submatrix (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inl i)))
        (G.submatrix (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)))
        (G.submatrix (fun i => Sum.inr (Sum.inr i)) (fun i => Sum.inr (Sum.inl i)))
        (G.submatrix (fun i => Sum.inr (Sum.inr i)) (fun i => Sum.inr (Sum.inr i)))) = G := by
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [B, G, seriesPencil, initial]
  have hz := SaturatedSchur.schur_zero_of_inverse_final_zero B B⁻¹ hB
    (G.submatrix Sum.inl (fun i => Sum.inr (Sum.inl i)))
    (G.submatrix Sum.inl (fun i => Sum.inr (Sum.inr i)))
    (G.submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl)
    (G.submatrix (fun i => Sum.inr (Sum.inr i)) Sum.inl)
    (G.submatrix (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inl i)))
    (G.submatrix (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inr i)))
    (G.submatrix (fun i => Sum.inr (Sum.inr i)) (fun i => Sum.inr (Sum.inl i)))
    (G.submatrix (fun i => Sum.inr (Sum.inr i)) (fun i => Sum.inr (Sum.inr i)))
    J (by rw [hblock]; exact hGJ) hDD
  have hKK : G.submatrix (fun i => Sum.inr (Sum.inl i)) (fun i => Sum.inr (Sum.inl i)) =
      (PowerSeries.X : PowerSeries K) • (G₁.submatrix (fun i => Sum.inr (Sum.inl i))
        (fun i => Sum.inr (Sum.inl i))).map PowerSeries.C := by
    ext i j
    simp [G, seriesPencil, initial]
  have hKB : G.submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl =
      (PowerSeries.X : PowerSeries K) • (G₁.submatrix (fun i => Sum.inr (Sum.inl i)) Sum.inl).map PowerSeries.C := by
    ext i j
    simp [G, seriesPencil, initial]
  have hBK : G.submatrix Sum.inl (fun i => Sum.inr (Sum.inl i)) =
      (PowerSeries.X : PowerSeries K) • (G₁.submatrix Sum.inl (fun i => Sum.inr (Sum.inl i))).map PowerSeries.C := by
    ext i j
    simp [G, seriesPencil, initial]
  simp only [hKK, hKB, hBK, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two] at hz
  exact cancel_formal_parameter _ _ hz

end HessianTheorem11.SaturatedResolvent
