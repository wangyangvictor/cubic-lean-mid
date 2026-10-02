import TranslatedDepthSeven.SalbergerAffinePacketMembership
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Complete affine lines in a displayed rational projective plane

Three integral chart points and their two divided differences supply
literal affine directions.  A rational combination of those directions
remains a direction of the same plane.  This is proved in the original
coordinates by a submodule identity, retaining the actual divisor.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The affine line in a rational combination of divided differences lies
in the same displayed linear projective cone. No primitivity, plane count,
or dimension assertion is needed for this incidence statement. -/
theorem integralAffineChartLine_mem_of_dividedDifferences
    {n : ℕ} (L : Submodule ℚ (Fin (n + 1) → ℚ))
    (base z z₁ z₂ v w h : IntVector n) (q : ℕ) (hq : 0 < q)
    (hbase : (fun i ↦ (integralAffineChartVector base i : ℚ)) ∈ L)
    (hz : (fun i ↦ (integralAffineChartVector z i : ℚ)) ∈ L)
    (hz₁ : (fun i ↦ (integralAffineChartVector z₁ i : ℚ)) ∈ L)
    (hz₂ : (fun i ↦ (integralAffineChartVector z₂ i : ℚ)) ∈ L)
    (hv : ∀ i, z₁ i = base i + q * v i)
    (hw : ∀ i, z₂ i = base i + q * w i)
    (a b : ℤ) (r : ℚ)
    (hscale : ∀ i, (h i : ℚ) = r * ((a * v i + b * w i : ℤ) : ℚ))
    (t : ℤ) :
    (fun i ↦ (integralAffineChartVector (fun j ↦ z j + t * h j) i : ℚ)) ∈ L := by
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  let A : ℚ := (t : ℚ) * r * (a : ℚ) / (q : ℚ)
  let B : ℚ := (t : ℚ) * r * (b : ℚ) / (q : ℚ)
  have hmem := L.add_mem hz
    (L.add_mem
      (L.smul_mem A (L.sub_mem hz₁ hbase))
      (L.smul_mem B (L.sub_mem hz₂ hbase)))
  have hvector :
      (fun i ↦ (integralAffineChartVector z i : ℚ)) +
          (A • ((fun i ↦ (integralAffineChartVector z₁ i : ℚ)) -
            (fun i ↦ (integralAffineChartVector base i : ℚ))) +
          B • ((fun i ↦ (integralAffineChartVector z₂ i : ℚ)) -
            (fun i ↦ (integralAffineChartVector base i : ℚ)))) =
        (fun i ↦
          (integralAffineChartVector (fun j ↦ z j + t * h j) i : ℚ)) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [integralAffineChartVector]
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        integralAffineChartVector, Fin.cases_succ, Int.cast_add, Int.cast_mul]
      rw [hv j, hw j]
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
      rw [hscale j]
      simp only [Int.cast_add, Int.cast_mul]
      dsimp [A, B]
      field_simp [hqQ]
      <;> ring
  rw [hvector] at hmem
  exact hmem

end

end TranslatedDepthSeven
