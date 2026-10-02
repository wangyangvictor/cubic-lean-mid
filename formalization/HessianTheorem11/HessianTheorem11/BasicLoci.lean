import HessianTheorem11.GeometricInjectivity
import HessianTheorem11.AffineDimension

/-! Nonemptiness, rank attainment, and the actual rank-zero locus dimension. -/

noncomputable section
namespace HessianTheorem11
open MvPolynomial

theorem eval_origin_of_positive_homogeneous
    {K : Type*} [CommRing K] {n d : ℕ} {p : MvPolynomial (Fin n) K}
    (hp : p.IsHomogeneous d) (hd : d ≠ 0) : eval 0 p = 0 := by
  rw [eval_zero]
  change coeff 0 p = 0
  apply hp.coeff_eq_zero
  simpa using Ne.symm hd

theorem origin_mem_cubicLocus {n : ℕ} (F : AnisotropicCubic n) :
    0 ∈ cubicLocus F.polynomial :=
  eval_origin_of_positive_homogeneous (geometric_homogeneous F.homogeneous) (by norm_num)

theorem origin_mem_singularLocus {n : ℕ} (F : AnisotropicCubic n) :
    0 ∈ singularLocus F.polynomial := by
  ext i
  exact eval_origin_of_positive_homogeneous
    (geometric_homogeneous F.homogeneous).pderiv (by norm_num)

theorem onCubicRanks_nonempty {n : ℕ} (F : AnisotropicCubic n) :
    (onCubicRanks F.polynomial).Nonempty :=
  ⟨_, 0, origin_mem_cubicLocus F, rfl⟩

/-- The rank supremum used by this development is an attained maximum.
Identifying it with the source's generic-point rank still uses irreducibility. -/
theorem genericHessianRank_attained {n : ℕ} (F : AnisotropicCubic n) :
    ∃ x ∈ cubicLocus F.polynomial,
      (hessian (geometricPolynomial F.polynomial) x).rank = genericHessianRank F.polynomial :=
  Nat.sSup_mem (onCubicRanks_nonempty F) (onCubicRanks_bddAbove F.polynomial)

theorem rank_lower_bound_iff_witness {n r : ℕ} (F : AnisotropicCubic n) :
    r ≤ genericHessianRank F.polynomial ↔
      ∃ x ∈ cubicLocus F.polynomial, r ≤ (hessian (geometricPolynomial F.polynomial) x).rank := by
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := genericHessianRank_attained F
    exact ⟨x, hx, he ▸ h⟩
  · rintro ⟨x, hx, h⟩
    exact h.trans (rank_le_genericHessianRank F.polynomial hx)

theorem singularDimension_nonnegative {n : ℕ} (F : AnisotropicCubic n) :
    0 ≤ singularDimension F.polynomial :=
  affineDimension_nonneg_of_nonempty ⟨0, origin_mem_singularLocus F⟩

theorem incidenceDimension_nonnegative {n : ℕ} (F : RationalPolynomial n) :
    0 ≤ incidenceDimension F :=
  affineDimension_nonneg_of_nonempty ⟨_, incidence_contains_zero_right F 0⟩

theorem rank_zero_locus_dimension {n : ℕ} (F : AnisotropicCubic n) :
    affineDimension (rankAtMostLocus F.polynomial 0) = 0 := by
  rw [rankAtMost_zero_locus F, affineDimension_origin]

end HessianTheorem11
