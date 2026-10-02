import TranslatedDepthSeven.HomogeneousIdealBridge
import TranslatedDepthSeven.RationalProjectiveLinearSpace

/-!
# Exact projective sections by rational linear equations

For a rational matrix `A`, this file writes each row as an explicit
homogeneous linear polynomial and projectivizes the literal kernel of
`A.mulVecLin`.  It then proves that adjoining the row polynomials to a finite
homogeneous equation family cuts out exactly the set-theoretic intersection
with that projective linear subspace.  The corresponding generated-ideal
identity is also proved exactly.

No dimension, codimension, saturation, component, or degree assertion is
made here.
-/

namespace TranslatedDepthSeven

noncomputable section

open scoped BigOperators LinearAlgebra.Projectivization

open Finset Matrix MvPolynomial

/-- The homogeneous linear polynomial whose coefficients are the entries
of row `r` of `A`. -/
def rationalMatrixRowLinearPolynomial {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (r : Fin c) :
    MvPolynomial (Fin N) ℚ :=
  ∑ j, MvPolynomial.C (A r j) * MvPolynomial.X j

/-- The literal finite family of all row linear polynomials of `A`. -/
def rationalMatrixRowLinearEquationFamily {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) :
    Finset (MvPolynomial (Fin N) ℚ) := by
  classical
  exact Finset.univ.image (rationalMatrixRowLinearPolynomial A)

/-- Every row equation is homogeneous of degree one. -/
theorem rationalMatrixRowLinearPolynomial_isHomogeneous {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (r : Fin c) :
    (rationalMatrixRowLinearPolynomial A r).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
  intro j _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- Evaluation of a row polynomial is exactly the corresponding coordinate
of the matrix-vector product. -/
theorem eval_rationalMatrixRowLinearPolynomial {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (r : Fin c) (x : Fin N → ℚ) :
    MvPolynomial.eval x (rationalMatrixRowLinearPolynomial A r) =
      (A *ᵥ x) r := by
  simp [rationalMatrixRowLinearPolynomial, Matrix.mulVec, dotProduct]

/-- The actual projectivization of the literal kernel of `A.mulVecLin`. -/
def projectivizationOfRationalMatrixKernel {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) :
    Projectivization.Subspace ℚ (Fin N → ℚ) :=
  (LinearMap.ker A.mulVecLin).projectivization

/-- Membership of a displayed nonzero representative in the projectivized
kernel is exactly the matrix equation `A x = 0`. -/
@[simp]
theorem mk_mem_projectivizationOfRationalMatrixKernel_iff {c N : ℕ}
    (A : Matrix (Fin c) (Fin N) ℚ) (x : Fin N → ℚ) (hx : x ≠ 0) :
    Projectivization.mk ℚ x hx ∈
        projectivizationOfRationalMatrixKernel A ↔
      A *ᵥ x = 0 := by
  rfl

/-- This projectivized kernel is exactly the previously defined rational
projective linear space attached to `A`. -/
theorem projectivizationOfRationalMatrixKernel_eq_rationalProjectiveLinearSpace
    {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℚ) :
    projectivizationOfRationalMatrixKernel A =
      rationalProjectiveLinearSpace A :=
  rfl

/-- The finite common projective zero locus of equations in the displayed
projective coordinate space.  Homogeneity hypotheses are supplied to the
theorems that use representative-independence. -/
def finiteProjectiveCommonZeroLocusInCoordinates {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) ℚ)) :
    Set (Projectivization ℚ (Fin N → ℚ)) :=
  {P | ∀ f ∈ equations, P ∈ homogeneousProjectiveHypersurface f}

@[simp]
theorem mem_finiteProjectiveCommonZeroLocusInCoordinates_iff {N : ℕ}
    (equations : Finset (MvPolynomial (Fin N) ℚ))
    (P : Projectivization ℚ (Fin N → ℚ)) :
    P ∈ finiteProjectiveCommonZeroLocusInCoordinates equations ↔
      ∀ f ∈ equations, P ∈ homogeneousProjectiveHypersurface f :=
  Iff.rfl

/-- The common projective zero locus of the row polynomials is exactly the
actual projectivization of the matrix kernel. -/
theorem finiteProjectiveCommonZeroLocus_rowLinearEquationFamily
    {c N : ℕ} (A : Matrix (Fin c) (Fin N) ℚ) :
    finiteProjectiveCommonZeroLocusInCoordinates
        (rationalMatrixRowLinearEquationFamily A) =
      (projectivizationOfRationalMatrixKernel A :
        Set (Projectivization ℚ (Fin N → ℚ))) := by
  classical
  ext P
  let x : Fin N → ℚ := P.rep
  have hx : x ≠ 0 := P.rep_nonzero
  have hmk : Projectivization.mk ℚ x hx = P := Projectivization.mk_rep P
  constructor
  · intro hrows
    have hAx : A *ᵥ x = 0 := by
      funext r
      have hmem : rationalMatrixRowLinearPolynomial A r ∈
          rationalMatrixRowLinearEquationFamily A := by
        exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
      have hProw := hrows _ hmem
      have hEval :
          MvPolynomial.eval x (rationalMatrixRowLinearPolynomial A r) = 0 :=
        (mk_mem_homogeneousProjectiveHypersurface_iff
          (rationalMatrixRowLinearPolynomial A r) 1
          (rationalMatrixRowLinearPolynomial_isHomogeneous A r) x hx).mp
          (by simpa only [hmk] using hProw)
      simpa [eval_rationalMatrixRowLinearPolynomial] using hEval
    have hmkKer : Projectivization.mk ℚ x hx ∈
        projectivizationOfRationalMatrixKernel A :=
      (mk_mem_projectivizationOfRationalMatrixKernel_iff A x hx).2 hAx
    simpa only [hmk] using hmkKer
  · intro hPker
    have hmkKer : Projectivization.mk ℚ x hx ∈
        projectivizationOfRationalMatrixKernel A := by
      simpa only [hmk] using hPker
    have hAx : A *ᵥ x = 0 :=
      (mk_mem_projectivizationOfRationalMatrixKernel_iff A x hx).1 hmkKer
    intro g hg
    obtain ⟨r, _hr, rfl⟩ := Finset.mem_image.mp hg
    rw [← hmk]
    apply (mk_mem_homogeneousProjectiveHypersurface_iff
      (rationalMatrixRowLinearPolynomial A r) 1
      (rationalMatrixRowLinearPolynomial_isHomogeneous A r) x hx).2
    change MvPolynomial.eval x (rationalMatrixRowLinearPolynomial A r) = 0
    rw [eval_rationalMatrixRowLinearPolynomial]
    exact congrFun hAx r

/-- Adjoining the row equations cuts out exactly the intersection of the
original common zero locus with the projectivized matrix kernel. -/
theorem finiteProjectiveCommonZeroLocus_union_rowLinearEquationFamily
    {c N : ℕ} (equations : Finset (MvPolynomial (Fin N) ℚ))
    (degree : MvPolynomial (Fin N) ℚ → ℕ)
    (_hhom : ∀ f ∈ equations, f.IsHomogeneous (degree f))
    (A : Matrix (Fin c) (Fin N) ℚ) :
    finiteProjectiveCommonZeroLocusInCoordinates
        (equations ∪ rationalMatrixRowLinearEquationFamily A) =
      finiteProjectiveCommonZeroLocusInCoordinates equations ∩
        (projectivizationOfRationalMatrixKernel A :
          Set (Projectivization ℚ (Fin N → ℚ))) := by
  rw [← finiteProjectiveCommonZeroLocus_rowLinearEquationFamily A]
  ext P
  simp only [mem_finiteProjectiveCommonZeroLocusInCoordinates_iff,
    Finset.mem_union, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun f hf ↦ h f (Or.inl hf), fun f hf ↦ h f (Or.inr hf)⟩
  · rintro ⟨hE, hA⟩ f (hf | hf)
    · exact hE f hf
    · exact hA f hf

/-- At generated-ideal level, adjoining the row equations is exactly the
supremum of the original generated ideal and the row-equation ideal. -/
theorem finiteEquationIdeal_union_rowLinearEquationFamily
    {c N : ℕ} (equations : Finset (MvPolynomial (Fin N) ℚ))
    (A : Matrix (Fin c) (Fin N) ℚ) :
    finiteEquationIdeal
        (equations ∪ rationalMatrixRowLinearEquationFamily A) =
      finiteEquationIdeal equations ⊔
        finiteEquationIdeal (rationalMatrixRowLinearEquationFamily A) := by
  rw [finiteEquationIdeal, finiteEquationIdeal, finiteEquationIdeal]
  rw [Finset.coe_union, Ideal.span_union]

end

end TranslatedDepthSeven
