import CubicTenVariables.GeometryTen
import HessianTheorem11.MatrixRankMinors

/-!
# A concrete rational Hessian minor for local rank selection

The proved geometric rank bound for an anisotropic ten-variable rational
cubic supplies a literal Hessian minor, of size at least eight, which is not
divisible by the cubic. Its coefficients are rational. Over every extension
field of ℚ, nonvanishing of this same polynomial forces actual Hessian rank
at least eight.

No p-adic point, avoidance theorem, or local-solubility assertion is assumed
or proved here. The row and column selections are explicit and need not be
the same; thus this is not a claim about principal minors.
-/

noncomputable section

universe u

namespace CubicTenVariables.RationalHessianMinor

open MvPolynomial HessianTheorem11

/-- The actual determinant polynomial of a selected square Hessian minor. -/
def hessianMinor {K : Type*} [CommRing K] {n r : ℕ}
    (F : MvPolynomial (Fin n) K) (rows cols : Fin r → Fin n) :
    MvPolynomial (Fin n) K :=
  ((hessianPolynomial F).submatrix rows cols).det

/-- Coefficient-extension evaluation of the minor polynomial is exactly
the determinant of the corresponding submatrix of the evaluated Hessian. -/
theorem eval₂_hessianMinor {K L : Type*} [CommRing K] [CommRing L]
    {n r : ℕ} (φ : K →+* L) (F : MvPolynomial (Fin n) K)
    (rows cols : Fin r → Fin n) (x : Fin n → L) :
    eval₂ φ x (hessianMinor F rows cols) =
      ((hessian (map φ F) x).submatrix rows cols).det := by
  change (eval₂Hom φ x) ((hessianPolynomial F).submatrix rows cols).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [hessian, hessianPolynomial, pderiv_map, eval_map]

/-- A nonzero value of a selected rational Hessian minor forces at least
its size as Hessian rank over every extension field of ℚ. -/
theorem size_le_rank_of_eval₂_ne_zero
    {K : Type*} [Field K] [Algebra ℚ K] {n r : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (rows cols : Fin r → Fin n)
    (x : Fin n → K)
    (hx : eval₂ (algebraMap ℚ K) x (hessianMinor F rows cols) ≠ 0) :
    r ≤ (hessian (map (algebraMap ℚ K) F) x).rank := by
  apply MatrixRankMinors.minor_size_le_rank _ rows cols
  rwa [← eval₂_hessianMinor]

/-- A minor nonzero at an actual geometric zero of the cubic cannot be
polynomially divisible by that cubic over ℚ. -/
theorem not_dvd_of_geometric_minor_ne_zero {n r : ℕ}
    (F : MvPolynomial (Fin n) ℚ) (rows cols : Fin r → Fin n)
    (x : GeometricPoint n) (hx : x ∈ cubicLocus F)
    (hd : ((hessian (geometricPolynomial F) x).submatrix rows cols).det ≠ 0) :
    ¬ F ∣ hessianMinor F rows cols := by
  have hFx : eval₂ (algebraMap ℚ GeometricField) x F = 0 := by
    simpa only [cubicLocus, Set.mem_setOf_eq, geometricPolynomial, eval_map] using hx
  have hDx : eval₂ (algebraMap ℚ GeometricField) x (hessianMinor F rows cols) ≠ 0 := by
    simpa only [eval₂_hessianMinor, geometricPolynomial] using hd
  rintro ⟨G, hG⟩
  apply hDx
  rw [hG, eval₂_mul, hFx, zero_mul]

/-- A rational anisotropic cubic in ten variables admits a displayed
minor of size at least eight which is nontrivial on the cubic. The same
rational polynomial detects rank at least eight over any field extension. -/
theorem exists_rational_hessian_minor (F : AnisotropicCubic 10) :
    ∃ (r : ℕ) (rows cols : Fin r → Fin 10),
      8 ≤ r ∧ ¬ F.polynomial ∣ hessianMinor F.polynomial rows cols ∧
      ∀ (K : Type u) [Field K] [Algebra ℚ K] (x : Fin 10 → K),
        eval₂ (algebraMap ℚ K) x (hessianMinor F.polynomial rows cols) ≠ 0 →
        8 ≤ (hessian (map (algebraMap ℚ K) F.polynomial) x).rank := by
  obtain ⟨x, hx, hr⟩ := genericHessianRank_attained F
  obtain ⟨rows, cols, hd⟩ :=
    MatrixRankMinors.exists_rank_minor (hessian (geometricPolynomial F.polynomial) x)
  have he : 8 ≤ (hessian (geometricPolynomial F.polynomial) x).rank := by
    rw [hr]
    exact Geometry.genericHessianRank_ge_eight F
  refine ⟨_, rows, cols, he,
    not_dvd_of_geometric_minor_ne_zero F.polynomial rows cols x hx hd, ?_⟩
  intro K _ _ y hy
  exact he.trans (size_le_rank_of_eval₂_ne_zero F.polynomial rows cols y hy)

end CubicTenVariables.RationalHessianMinor
