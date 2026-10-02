import HessianTheorem11.PolynomialSchurVanishing
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.MvPolynomial.Funext

/-! Rank bounds on every point of an affine line give exact identities of
matrix power series. This is polynomial identity and bordered-minor algebra. -/
noncomputable section
namespace HessianTheorem11.PencilSchurVanishing
open Matrix MvPolynomial PolynomialSchurVanishing

variable {K R σ α κ : Type*} [Field K] [Infinite K] [CommRing R]
  [Fintype σ] [Fintype α] [Fintype κ] [DecidableEq κ]

theorem schur_eq_zero_of_everywhere_rank_le
    (A : Matrix α α (MvPolynomial σ K)) (C : Matrix α κ (MvPolynomial σ K))
    (D : Matrix κ α (MvPolynomial σ K)) (G : Matrix κ κ (MvPolynomial σ K))
    (hrank : ∀ x : σ → K,
      ((Matrix.fromBlocks A C D G).map (eval x)).rank ≤ Fintype.card κ)
    (φ : MvPolynomial σ K →+* R) (J : Matrix κ κ R) (hGJ : G.map φ * J = 1) :
    A.map φ - C.map φ * J * D.map φ = 0 := by
  have hz (i j : α) : (bordered A C D G i j).det = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero, RingHom.map_det, bordered_eq_submatrix]
    apply det_eq_zero_of_rank_lt
    have h := (rank_submatrix_le ((Matrix.fromBlocks A C D G).map (eval x))
      (Sum.elim (fun _ : Fin 1 => Sum.inl i) Sum.inr)
      (Sum.elim (fun _ : Fin 1 => Sum.inl j) Sum.inr)).trans (hrank x)
    simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_comm] using
      Nat.lt_of_le_of_lt h (Nat.lt_add_one (Fintype.card κ))
  ext i j
  have h := congrArg φ (hz i j)
  rw [map_zero, RingHom.map_det] at h
  change ((bordered A C D G i j).map φ).det = 0 at h
  rw [bordered_map, det_bordered _ _ _ _ J hGJ i j] at h
  apply (Matrix.isUnit_det_of_right_inverse hGJ).mul_left_cancel
  simpa only [Matrix.zero_apply, mul_zero] using h

omit [Infinite K] [Fintype σ] [Fintype α] [Fintype κ] [DecidableEq κ] in
def pencil {ι υ : Type*} (M₀ M₁ : Matrix ι υ K) : Matrix ι υ (MvPolynomial (Fin 1) K) :=
  M₀.map C + (X 0 : MvPolynomial (Fin 1) K) • M₁.map C

omit [Infinite K] [Fintype σ] [Fintype α] [Fintype κ] [DecidableEq κ] in
def seriesPencil {ι υ : Type*} (M₀ M₁ : Matrix ι υ K) : Matrix ι υ (PowerSeries K) :=
  M₀.map PowerSeries.C + (PowerSeries.X : PowerSeries K) • M₁.map PowerSeries.C

omit [Infinite K] [Fintype σ] [Fintype α] [Fintype κ] [DecidableEq κ] in
theorem pencil_eval {ι υ : Type*} (M₀ M₁ : Matrix ι υ K) (x : Fin 1 → K) :
    (pencil M₀ M₁).map (eval x) = M₀ + x 0 • M₁ := by
  ext i j
  simp [pencil]

omit [Infinite K] [Fintype σ] [Fintype α] [Fintype κ] [DecidableEq κ] in
theorem pencil_series {ι υ : Type*} (M₀ M₁ : Matrix ι υ K) :
    (pencil M₀ M₁).map (eval₂Hom PowerSeries.C (fun _ => PowerSeries.X)) =
      seriesPencil M₀ M₁ := by
  ext i j
  simp [pencil, seriesPencil]

theorem pencil_schur_eq_zero
    (A₀ A₁ : Matrix α α K) (C₀ C₁ : Matrix α κ K)
    (D₀ D₁ : Matrix κ α K) (G₀ G₁ : Matrix κ κ K)
    (hrank : ∀ t : K, (Matrix.fromBlocks (A₀+t•A₁) (C₀+t•C₁)
      (D₀+t•D₁) (G₀+t•G₁)).rank ≤ Fintype.card κ)
    (J : Matrix κ κ (PowerSeries K)) (hGJ : seriesPencil G₀ G₁ * J = 1) :
    seriesPencil A₀ A₁ - seriesPencil C₀ C₁ * J * seriesPencil D₀ D₁ = 0 := by
  have h := schur_eq_zero_of_everywhere_rank_le
    (pencil A₀ A₁) (pencil C₀ C₁) (pencil D₀ D₁) (pencil G₀ G₁)
    (fun x => ?_) (eval₂Hom PowerSeries.C (fun _ => PowerSeries.X)) J
    (by simpa only [pencil_series] using hGJ)
  · simpa only [pencil_series] using h
  · simpa only [Matrix.fromBlocks_map, pencil_eval] using hrank (x 0)

omit [Infinite K] [Fintype σ] [Fintype α] in
theorem seriesPencil_isUnit_det (G₀ G₁ : Matrix κ κ K) (h₀ : IsUnit G₀.det) :
    IsUnit (seriesPencil G₀ G₁).det := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [RingHom.map_det]
  have h : (seriesPencil G₀ G₁).map PowerSeries.constantCoeff = G₀ := by
    ext i j
    simp [seriesPencil]
  change IsUnit ((seriesPencil G₀ G₁).map PowerSeries.constantCoeff).det
  rw [h]
  exact h₀

end HessianTheorem11.PencilSchurVanishing
