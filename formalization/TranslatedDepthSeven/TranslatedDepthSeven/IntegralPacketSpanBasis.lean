import TranslatedDepthSeven.CramerSpanEquations
import TranslatedDepthSeven.Parameters

/-!
# An integral basis for the direction span of a finite packet

The tangent-minor argument bounds the dimension of the rational span of
integral point differences.  This file chooses a basis from the differences
themselves.  Consequently the basis matrix remains integral and inherits the
original coordinate bound.  A nonsingular pivot minor can then be selected,
so the explicit Cramer equations apply without any denominator-clearing
argument.
-/

namespace TranslatedDepthSeven

noncomputable section

/-- The rational direction determined by an integral point and an integral
base point. -/
def rationalIntegralDifference {N : ℕ}
    (base z : IntVector N) : Fin N → ℚ :=
  fun j ↦ ((z j - base j : ℤ) : ℚ)

/-- Integral row matrix of a selected family of point differences. -/
def integralDifferenceMatrix {N r : ℕ}
    (base : IntVector N) (point : Fin r → IntVector N) :
    Matrix (Fin r) (Fin N) ℤ :=
  fun i j ↦ point i j - base j

@[simp]
theorem integralDifferenceMatrix_map_row {N r : ℕ}
    (base : IntVector N) (point : Fin r → IntVector N) (i : Fin r) :
    ((integralDifferenceMatrix base point).map ((↑) : ℤ → ℚ)).row i =
      rationalIntegralDifference base (point i) := by
  rfl

/-- Containment of all packet points in an affine subspace bounds the
rational span of their integral differences by the dimension of its
direction. -/
theorem finrank_span_rationalIntegralDifference_le_of_mem_affineSubspace
    {N : ℕ} (Z : Finset (IntVector N)) (base : IntVector N)
    (hbase : base ∈ Z) (A : AffineSubspace ℚ (Fin N → ℚ))
    (hmem : ∀ z ∈ Z, (fun j ↦ (z j : ℚ)) ∈ A) :
    Module.finrank ℚ
        (Submodule.span ℚ
          (Set.range fun z : {z // z ∈ Z} ↦
            rationalIntegralDifference base z.1)) ≤
      Module.finrank ℚ A.direction := by
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨z, rfl⟩
  have hz := hmem z.1 z.2
  have hb := hmem base hbase
  have hdiff := A.vsub_mem_direction hz hb
  have heq : rationalIntegralDifference base z.1 =
      (fun j ↦ (z.1 j : ℚ)) - fun j ↦ (base j : ℚ) := by
    funext j
    simp [rationalIntegralDifference]
  change rationalIntegralDifference base z.1 ∈ A.direction
  rw [heq]
  simpa [vsub_eq_sub] using hdiff

/-- Select a basis of the rational difference span from the packet itself,
and then select a nonsingular integral pivot minor.  The integer basis rows
retain the original coordinate bound exactly. -/
theorem exists_integralDifferenceBasis_with_pivot
    {N d M : ℕ} (Z : Finset (IntVector N)) (base : IntVector N)
    (hdim : Module.finrank ℚ
      (Submodule.span ℚ
        (Set.range fun z : {z // z ∈ Z} ↦
          rationalIntegralDifference base z.1)) ≤ d)
    (hcoord : ∀ z ∈ Z, ∀ j,
      (z j - base j).natAbs ≤ M) :
    ∃ r : ℕ, ∃ point : Fin r → {z // z ∈ Z},
      ∃ J : Fin r ↪ Fin N,
        r ≤ d ∧
        (selectedIntegralPivot
          (integralDifferenceMatrix base (fun i ↦ (point i).1)) J).det ≠ 0 ∧
        Submodule.span ℚ
            (Set.range
              ((integralDifferenceMatrix base
                (fun i ↦ (point i).1)).map ((↑) : ℤ → ℚ)).row) =
          Submodule.span ℚ
            (Set.range fun z : {z // z ∈ Z} ↦
              rationalIntegralDifference base z.1) ∧
        ∀ i j,
          (integralDifferenceMatrix base
            (fun i ↦ (point i).1) i j).natAbs ≤ M := by
  classical
  let v : {z // z ∈ Z} → Fin N → ℚ :=
    fun z ↦ rationalIntegralDifference base z.1
  let r := Module.finrank ℚ (Submodule.span ℚ (Set.range v))
  obtain ⟨f, hfmem, hspan, hlin⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  choose point hpoint using hfmem
  let B : Matrix (Fin r) (Fin N) ℤ :=
    integralDifferenceMatrix base (fun i ↦ (point i).1)
  have hBrow : (B.map ((↑) : ℤ → ℚ)).row = f := by
    funext i
    simpa [B, v] using hpoint i
  have hBlin : LinearIndependent ℚ (B.map ((↑) : ℤ → ℚ)).row := by
    rw [hBrow]
    exact hlin
  obtain ⟨cols, hcols, hminor⟩ :=
    TangentPacketSpan.exists_selectedMinor_ne_zero_of_linearIndependent_rows
      (B.map ((↑) : ℤ → ℚ)) hBlin
  let J : Fin r ↪ Fin N := ⟨cols, hcols⟩
  have hdet : (selectedIntegralPivot B J).det ≠ 0 := by
    intro hzero
    apply hminor
    have hmap := (Int.castRingHom ℚ).map_det (selectedIntegralPivot B J)
    rw [hzero, map_zero] at hmap
    simpa [selectedIntegralPivot, J] using hmap.symm
  refine ⟨r, point, J, ?_, hdet, ?_, ?_⟩
  · simpa [r, v] using hdim
  · rw [hBrow]
    simpa [v] using hspan
  · intro i j
    exact hcoord (point i).1 (point i).2 j

/-- The preceding dimension comparison followed by the integral basis
selection, in the form used for a packet already known to lie in an affine
`d`-plane. -/
theorem exists_integralDifferenceBasis_with_pivot_of_affineSubspace
    {N d M : ℕ} (Z : Finset (IntVector N)) (base : IntVector N)
    (hbase : base ∈ Z) (A : AffineSubspace ℚ (Fin N → ℚ))
    (hAdim : Module.finrank ℚ A.direction ≤ d)
    (hmem : ∀ z ∈ Z, (fun j ↦ (z j : ℚ)) ∈ A)
    (hcoord : ∀ z ∈ Z, ∀ j, (z j - base j).natAbs ≤ M) :
    ∃ r : ℕ, ∃ point : Fin r → {z // z ∈ Z},
      ∃ J : Fin r ↪ Fin N,
        r ≤ d ∧
        (selectedIntegralPivot
          (integralDifferenceMatrix base (fun i ↦ (point i).1)) J).det ≠ 0 ∧
        Submodule.span ℚ
            (Set.range
              ((integralDifferenceMatrix base
                (fun i ↦ (point i).1)).map ((↑) : ℤ → ℚ)).row) =
          Submodule.span ℚ
            (Set.range fun z : {z // z ∈ Z} ↦
              rationalIntegralDifference base z.1) ∧
        ∀ i j,
          (integralDifferenceMatrix base
            (fun i ↦ (point i).1) i j).natAbs ≤ M := by
  apply exists_integralDifferenceBasis_with_pivot Z base
  · exact (finrank_span_rationalIntegralDifference_le_of_mem_affineSubspace
      Z base hbase A hmem).trans hAdim
  · exact hcoord

end

end TranslatedDepthSeven
