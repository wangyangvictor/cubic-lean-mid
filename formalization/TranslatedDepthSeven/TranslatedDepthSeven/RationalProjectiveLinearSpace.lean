import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Projectivization.Subspace
import TranslatedDepthSeven.PrimitiveRationalVectorHeight

/-!
# Rational projective linear spaces given by equations

This file records the literal matrix model used for rational projective
linear spaces.  A matrix `A : Matrix (Fin c) (Fin N) ℚ` cuts out the
linear cone `ker A.mulVecLin` in `ℚ^N`; a nonzero vector in this cone is a
rational representative of a point of the associated projective linear
space.

No custom geometric interface is introduced: the affine cone is the literal
kernel, and the projective space is Mathlib's projectivization of that
submodule.  In particular, the main invariance theorem below says directly
that replacing a basis of the row equations by an invertible rational linear
combination leaves the kernel unchanged.
-/

namespace TranslatedDepthSeven

noncomputable section

open Matrix
open scoped LinearAlgebra.Projectivization

/-- The affine cone cut out by the homogeneous rational equations in the
rows of `A`. -/
def rationalLinearCone {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℚ) :
    Submodule ℚ (Fin N → ℚ) :=
  LinearMap.ker A.mulVecLin

/-- The actual rational projective subspace obtained by projectivizing the
literal matrix kernel. -/
def rationalProjectiveLinearSpace {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) :
    Projectivization.Subspace ℚ (Fin N → ℚ) :=
  (rationalLinearCone A).projectivization

@[simp]
theorem mem_rationalLinearCone_iff {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (x : Fin N → ℚ) :
    x ∈ rationalLinearCone A ↔ A *ᵥ x = 0 := by
  rfl

/-- A literal nonzero rational vector representing a projective point in the
linear space cut out by `A`. -/
def IsRationalProjectiveRepresentative {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (x : Fin N → ℚ) : Prop :=
  x ≠ 0 ∧ x ∈ rationalLinearCone A

theorem isRationalProjectiveRepresentative_iff {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (x : Fin N → ℚ) :
    IsRationalProjectiveRepresentative A x ↔ x ≠ 0 ∧ A *ᵥ x = 0 := by
  rfl

/-- Membership of a projective point is exactly membership of any nonzero
representative in the affine cone, hence exactly the displayed matrix
equation. -/
theorem projectivization_mk_mem_rationalProjectiveLinearSpace_iff
    {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℚ)
    (x : Fin N → ℚ) (hx : x ≠ 0) :
    Projectivization.mk ℚ x hx ∈ rationalProjectiveLinearSpace A ↔
      A *ᵥ x = 0 := by
  rfl

/-- Nonzero scalar multiples represent the same membership condition. -/
theorem isRationalProjectiveRepresentative_smul_iff {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (x : Fin N → ℚ)
    (r : ℚ) (hr : r ≠ 0) :
    IsRationalProjectiveRepresentative A (r • x) ↔
      IsRationalProjectiveRepresentative A x := by
  constructor
  · rintro ⟨hrx, hx⟩
    refine ⟨?_, ?_⟩
    · intro hx0
      exact hrx (by simp [hx0])
    · have hback := (rationalLinearCone A).smul_mem r⁻¹ hx
      simpa [hr] using hback
  · rintro ⟨hx0, hx⟩
    exact ⟨smul_ne_zero hr hx0, (rationalLinearCone A).smul_mem r hx⟩

/-- An invertible rational change of basis among the equations leaves the
cut-out affine cone unchanged. -/
theorem rationalLinearCone_mul_left {c N : ℕ}
    (U : Matrix (Fin c) (Fin c) ℚ) (A : Matrix (Fin c) (Fin N) ℚ)
    (hU : U.det ≠ 0) :
    rationalLinearCone (U * A) = rationalLinearCone A := by
  ext x
  simp only [mem_rationalLinearCone_iff]
  constructor
  · intro hx
    exact (Matrix.mulVec_injective_iff_isUnit.mpr
      (U.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hU)))
        (by simpa using hx)
  · intro hx
    simpa using congrArg (fun y ↦ U *ᵥ y) hx

/-- The projective subspace itself is independent of an invertible rational
change of basis among the defining equations. -/
theorem rationalProjectiveLinearSpace_mul_left {c N : ℕ}
    (U : Matrix (Fin c) (Fin c) ℚ) (A : Matrix (Fin c) (Fin N) ℚ)
    (hU : U.det ≠ 0) :
    rationalProjectiveLinearSpace (U * A) =
      rationalProjectiveLinearSpace A := by
  simp only [rationalProjectiveLinearSpace, rationalLinearCone_mul_left U A hU]

/-- The same basis invariance stated directly for nonzero projective
representatives. -/
theorem isRationalProjectiveRepresentative_mul_left_iff {c N : ℕ}
    (U : Matrix (Fin c) (Fin c) ℚ) (A : Matrix (Fin c) (Fin N) ℚ)
    (hU : U.det ≠ 0) (x : Fin N → ℚ) :
    IsRationalProjectiveRepresentative (U * A) x ↔
      IsRationalProjectiveRepresentative A x := by
  simp only [IsRationalProjectiveRepresentative, rationalLinearCone_mul_left U A hU]

/-- The dimension of the affine cone is `N - rank A`. -/
theorem finrank_rationalLinearCone {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) :
    Module.finrank ℚ (rationalLinearCone A) = N - A.rank := by
  have hnullity := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hrange : Module.finrank ℚ (LinearMap.range A.mulVecLin) = A.rank := by
    rw [Matrix.range_mulVecLin, ← Matrix.rank_eq_finrank_span_cols]
  have hdim : Module.finrank ℚ (Fin N → ℚ) = N := by simp
  rw [hrange, hdim] at hnullity
  exact Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using hnullity)

/-- With independent equations, the cone has the expected codimension. -/
theorem finrank_rationalLinearCone_of_full_row_rank {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (hA : A.rank = c) :
    Module.finrank ℚ (rationalLinearCone A) = N - c := by
  simpa [hA] using finrank_rationalLinearCone A

/-! ## Plücker minors and their literal primitive integral normalization -/

/-- An index for an ordered maximal minor.  Using embeddings rather than
subsets avoids making any auxiliary ordering choice; reordering an embedding
only changes the sign of the corresponding determinant. -/
abbrev RationalPluckerIndex (c N : ℕ) := Fin c ↪ Fin N

/-- The maximal minor indexed by the selected columns. -/
def rationalPluckerCoordinate {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (J : RationalPluckerIndex c N) : ℚ :=
  (A.submatrix id J).det

/-- A matrix of full row rank has a nonzero maximal minor.

The proof makes no choice of a preferred Gaussian-elimination algorithm.  It
extracts a basis from the finite family of columns, reindexes that basis by
`Fin c`, and uses the usual equivalence between independent columns and an
invertible square matrix.  In particular, the statement also covers `c = 0`
(the unique empty minor has determinant one).  If `c > N`, the full-row-rank
hypothesis is impossible by `Matrix.rank_le_width`, so no exceptional case is
silently hidden in the formulation. -/
theorem exists_rationalPluckerCoordinate_ne_zero_of_full_row_rank
    {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℚ) (hA : A.rank = c) :
    ∃ J : RationalPluckerIndex c N, rationalPluckerCoordinate A J ≠ 0 := by
  have hcN : c ≤ N := by
    rw [← hA]
    exact A.rank_le_width
  obtain ⟨κ, a, ha, hspan, hlin⟩ :=
    exists_linearIndependent' ℚ A.col
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = c := by
    calc
      Fintype.card κ =
          Module.finrank ℚ (Submodule.span ℚ (Set.range (A.col ∘ a))) :=
        linearIndependent_iff_card_eq_finrank_span.mp hlin
      _ = Module.finrank ℚ (Submodule.span ℚ (Set.range A.col)) := by
        rw [hspan]
      _ = A.rank := (Matrix.rank_eq_finrank_span_cols A).symm
      _ = c := hA
  let e : Fin c ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let J : RationalPluckerIndex c N :=
    ⟨fun i ↦ a (e i), ha.comp e.injective⟩
  refine ⟨J, ?_⟩
  have hcols : LinearIndependent ℚ (A.submatrix id J).col := by
    have he : LinearIndependent ℚ ((A.col ∘ a) ∘ e) :=
      hlin.comp e e.injective
    simpa only [Matrix.col, Matrix.submatrix, id_eq, Function.comp_apply, J]
      using he
  have hunit : IsUnit (A.submatrix id J) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  exact ((A.submatrix id J).isUnit_iff_isUnit_det.mp hunit).ne_zero

/-- An equation-basis change multiplies every Plücker minor by the same
nonzero scalar, namely the determinant of the basis-change matrix. -/
theorem rationalPluckerCoordinate_mul_left {c N : ℕ}
    (U : Matrix (Fin c) (Fin c) ℚ) (A : Matrix (Fin c) (Fin N) ℚ)
    (J : RationalPluckerIndex c N) :
    rationalPluckerCoordinate (U * A) J =
      U.det * rationalPluckerCoordinate A J := by
  rw [rationalPluckerCoordinate, rationalPluckerCoordinate,
    Matrix.submatrix_mul U A id id J Function.bijective_id, det_mul]
  simp

/-- The finite row vector containing all ordered maximal minors. -/
def rationalPluckerRow {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℚ) :
    Matrix (Fin 1) (RationalPluckerIndex c N) ℚ :=
  fun _ J ↦ rationalPluckerCoordinate A J

/-- A positive common denominator for all Plücker minors. -/
def rationalPluckerDenominator {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) : ℕ :=
  (rationalPluckerRow A).den

/-- The integral maximal-minor vector obtained by clearing the canonical
LCM denominator supplied by `Matrix.den`. -/
def integralPluckerCoordinate {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (J : RationalPluckerIndex c N) : ℤ :=
  (rationalPluckerRow A).num (0 : Fin 1) J

theorem rationalPluckerDenominator_ne_zero {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) :
    rationalPluckerDenominator A ≠ 0 := by
  exact Matrix.den_ne_zero (rationalPluckerRow A)

/-- Clearing denominators recovers the original rational minor exactly. -/
theorem integralPluckerCoordinate_div_denominator {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (J : RationalPluckerIndex c N) :
    (integralPluckerCoordinate A J : ℚ) /
        (rationalPluckerDenominator A : ℚ) =
      rationalPluckerCoordinate A J := by
  exact Matrix.num_div_den (rationalPluckerRow A) (0 : Fin 1) J

theorem integralPluckerCoordinate_ne_zero_iff {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (J : RationalPluckerIndex c N) :
    integralPluckerCoordinate A J ≠ 0 ↔
      rationalPluckerCoordinate A J ≠ 0 := by
  rw [← integralPluckerCoordinate_div_denominator A J]
  simp [rationalPluckerDenominator_ne_zero A]

/-- The positive content (GCD of absolute values) of the cleared integral
minor vector. -/
def integralPluckerContent {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) : ℕ :=
  Finset.univ.gcd (fun J : RationalPluckerIndex c N ↦
    (integralPluckerCoordinate A J).natAbs)

theorem integralPluckerContent_dvd {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (J : RationalPluckerIndex c N) :
    integralPluckerContent A ∣ (integralPluckerCoordinate A J).natAbs := by
  exact Finset.gcd_dvd (Finset.mem_univ J)

/-- A signed primitive integral Plücker coordinate.  If all maximal minors
vanish, both the content and these coordinates are zero; the full-row-rank
case is the intended one. -/
def primitiveIntegralPluckerCoordinate {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (J : RationalPluckerIndex c N) : ℤ :=
  integralPluckerCoordinate A J / (integralPluckerContent A : ℤ)

theorem primitiveIntegralPluckerCoordinate_natAbs {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (J : RationalPluckerIndex c N) :
    (primitiveIntegralPluckerCoordinate A J).natAbs =
      (integralPluckerCoordinate A J).natAbs / integralPluckerContent A := by
  apply Int.natAbs_ediv_of_dvd
  exact Int.natCast_dvd.mpr (integralPluckerContent_dvd A J)

/-- The literal projective Plücker height: the maximum absolute value of the
primitive integral maximal-minor coordinates. -/
def rationalProjectiveLinearHeight {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) : ℕ :=
  Finset.univ.sup (fun J : RationalPluckerIndex c N ↦
    (primitiveIntegralPluckerCoordinate A J).natAbs)

/-- The Plücker-height definition is exactly the generic primitive height of
the finite rational vector of maximal minors. -/
theorem rationalProjectiveLinearHeight_eq_primitiveRationalVectorHeight
    {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℚ) :
    rationalProjectiveLinearHeight A =
      primitiveRationalVectorHeight
        (fun J : RationalPluckerIndex c N ↦
          rationalPluckerCoordinate A J) := by
  rfl

theorem primitiveIntegralPluckerCoordinate_le_height {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (J : RationalPluckerIndex c N) :
    (primitiveIntegralPluckerCoordinate A J).natAbs ≤
      rationalProjectiveLinearHeight A := by
  change (primitiveIntegralPluckerCoordinate A J).natAbs ≤
    Finset.univ.sup (fun J : RationalPluckerIndex c N ↦
      (primitiveIntegralPluckerCoordinate A J).natAbs)
  exact Finset.le_sup (α := ℕ) (β := RationalPluckerIndex c N)
    (s := Finset.univ)
    (f := fun J : RationalPluckerIndex c N ↦
      (primitiveIntegralPluckerCoordinate A J).natAbs)
    (Finset.mem_univ J)

/-- If one maximal minor is nonzero, the normalized integral Plücker vector
really is primitive: the GCD of its absolute coordinates is one. -/
theorem primitiveIntegralPluckerCoordinate_gcd_eq_one {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (J₀ : RationalPluckerIndex c N)
    (hJ₀ : integralPluckerCoordinate A J₀ ≠ 0) :
    Finset.univ.gcd (fun J : RationalPluckerIndex c N ↦
      (primitiveIntegralPluckerCoordinate A J).natAbs) = 1 := by
  simp only [primitiveIntegralPluckerCoordinate_natAbs]
  exact Finset.gcd_div_eq_one (Finset.mem_univ J₀)
    (Int.natAbs_ne_zero.mpr hJ₀)

theorem primitiveIntegralPluckerCoordinate_gcd_eq_one_of_minor_ne_zero
    {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℚ)
    (J₀ : RationalPluckerIndex c N)
    (hJ₀ : rationalPluckerCoordinate A J₀ ≠ 0) :
    Finset.univ.gcd (fun J : RationalPluckerIndex c N ↦
      (primitiveIntegralPluckerCoordinate A J).natAbs) = 1 := by
  exact primitiveIntegralPluckerCoordinate_gcd_eq_one A J₀
    ((integralPluckerCoordinate_ne_zero_iff A J₀).2 hJ₀)

/-- The literal primitive Plücker height is independent of every invertible
rational change of basis among the defining equations. -/
theorem rationalProjectiveLinearHeight_mul_left {c N : ℕ}
    (U : Matrix (Fin c) (Fin c) ℚ) (A : Matrix (Fin c) (Fin N) ℚ)
    (hU : U.det ≠ 0) :
    rationalProjectiveLinearHeight (U * A) =
      rationalProjectiveLinearHeight A := by
  let v : RationalPluckerIndex c N → ℚ :=
    fun J ↦ rationalPluckerCoordinate A J
  have hvec :
      (fun J : RationalPluckerIndex c N ↦
        rationalPluckerCoordinate (U * A) J) = U.det • v := by
    funext J
    simp only [rationalPluckerCoordinate_mul_left, Pi.smul_apply, smul_eq_mul, v]
  rw [rationalProjectiveLinearHeight_eq_primitiveRationalVectorHeight,
    rationalProjectiveLinearHeight_eq_primitiveRationalVectorHeight, hvec]
  change primitiveRationalVectorHeight (U.det • v) =
    primitiveRationalVectorHeight v
  by_cases hv : v = 0
  · simp [hv]
  · exact primitiveRationalVectorHeight_smul v U.det hv hU

end

end TranslatedDepthSeven
