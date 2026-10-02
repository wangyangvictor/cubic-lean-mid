import TranslatedDepthSeven.RationalSmoothPointLocalEquationExtraction
import TranslatedDepthSeven.RationalPointResidueField

/-!
# A finite Jacobian menu on the smooth rational locus

This file specializes the abstract conormal-selection theorem to a literal
finite generating family of an affine ideal.  At a smooth rational point,
once the residual differential dimension is specified, a subfamily of the
given equations and an equally sized set of coordinate variables have a
nonzero ordinary Jacobian minor.  The selected equations generate the exact
localized ideal.

The choices range over finite types.  Consequently the theorem supplies the
pointwise ingredient for a single finite menu of Jacobian charts; no
point-dependent equations are introduced.
-/

namespace TranslatedDepthSeven

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

open scoped TensorProduct
open MvPolynomial KaehlerDifferential IsLocalRing

universe u

/-- After identifying the residue field at a rational point with the ground
field, one canonical residual ambient coordinate is exactly the ordinary
partial derivative evaluated at that point. -/
theorem affineQuotientResidualAmbientCoordinate_equiv_eq_eval_pderiv
    {k : Type u} [Field k] {N : ℕ}
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom)
    (f : MvPolynomial (Fin N) k) (hf : f ∈ J) (i : Fin N) :
    affineQuotientRationalPointResidueFieldAlgEquiv J z hJ
        (affineQuotientResidualAmbientCoordinates J z hJ
          (((affineQuotientLocalExtension J z hJ).cotangentComplex.baseChange
            (ResidueField (AffineQuotientRationalPointLocalRing J z hJ)))
            ((1 : ResidueField
                (AffineQuotientRationalPointLocalRing J z hJ))
              ⊗ₜ[AffineQuotientRationalPointLocalRing J z hJ]
                Algebra.Extension.Cotangent.mk
                  (affineQuotientLocalKernelElement J z hJ f hf))) i) =
      MvPolynomial.eval z (MvPolynomial.pderiv i f) := by
  rw [affineQuotientResidualAmbientCoordinates_apply]
  let R := MvPolynomial (Fin N) k
  let A := R ⧸ J
  let x := affineQuotientRationalPoint J z hJ
  let Q : Ideal A := RingHom.ker x.toRingHom
  let L := Localization.AtPrime (affineEvaluationPrime z)
  let S := Localization.AtPrime Q
  let localMap := affineQuotientLocalRingAlgHom J z hJ
  have hlocal : localMap
      (algebraMap R L (MvPolynomial.pderiv i f)) =
      algebraMap A S
        (Ideal.Quotient.mk J (MvPolynomial.pderiv i f)) := by
    simpa only [R, A, Q, L, S, localMap,
      affineQuotientLocalRingAlgHom] using
      Localization.localRingHom_to_map
        (affineEvaluationPrime z) Q (Ideal.Quotient.mk J)
          (affineEvaluationPrime_eq_comap_affineQuotientPoint J z hJ)
            (MvPolynomial.pderiv i f)
  change rationalPointResidueFieldAlgEquiv x
      (algebraMap S (ResidueField S)
        (localMap (algebraMap R L (MvPolynomial.pderiv i f)))) = _
  rw [hlocal, ← IsScalarTower.algebraMap_apply A S (ResidueField S),
    rationalPointResidueFieldAlgEquiv_algebraMap,
    affineQuotientRationalPoint_mk]
  rw [MvPolynomial.aeval_eq_eval]

/-- A finite generating family of an affine ideal contains, at every smooth
rational point of residual differential dimension `s`, an expected-size
subfamily with a nonzero residual Jacobian minor in the canonical ambient
coordinates.  That subfamily generates the whole ideal after localization
at the point. -/
theorem exists_selected_affineIdeal_generators_and_residual_minor
    {k : Type u} [Field k] {N n s : ℕ}
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom)
    [Algebra.FormallySmooth k
      (AffineQuotientRationalPointLocalRing J z hJ)]
    (htarget : Module.finrank
      (ResidueField (AffineQuotientRationalPointLocalRing J z hJ))
      (ResidueField (AffineQuotientRationalPointLocalRing J z hJ)
        ⊗[AffineQuotientRationalPointLocalRing J z hJ]
          Ω[AffineQuotientRationalPointLocalRing J z hJ⁄k]) = s)
    (F : Fin n → MvPolynomial (Fin N) k)
    (hF : Ideal.span (Set.range F) = J) :
    ∃ rows : Fin (N - s) → Fin n,
      ∃ cols : Fin (N - s) → Fin N,
        Function.Injective rows ∧ Function.Injective cols ∧
          Matrix.det (Matrix.of (fun i j ↦
            affineQuotientResidualAmbientCoordinates J z hJ
              (((affineQuotientLocalExtension J z hJ).cotangentComplex.baseChange
                (ResidueField
                  (AffineQuotientRationalPointLocalRing J z hJ)))
                ((1 : ResidueField
                    (AffineQuotientRationalPointLocalRing J z hJ))
                  ⊗ₜ[AffineQuotientRationalPointLocalRing J z hJ]
                    Algebra.Extension.Cotangent.mk
                      (affineQuotientLocalKernelElement J z hJ
                        (F (rows i)) (hF.le
                          (Ideal.subset_span ⟨rows i, rfl⟩)))))
              (cols j))) ≠ 0 ∧
          Ideal.span (Set.range fun i ↦
            algebraMap (MvPolynomial (Fin N) k)
              (Localization.AtPrime (affineEvaluationPrime z))
                (F (rows i))) =
            (affineQuotientLocalExtension J z hJ).ker := by
  classical
  let Flocal : Fin n →
      Localization.AtPrime (affineEvaluationPrime z) := fun i ↦
    algebraMap (MvPolynomial (Fin N) k)
      (Localization.AtPrime (affineEvaluationPrime z)) (F i)
  have hFlocal : Ideal.span (Set.range Flocal) =
      (affineQuotientLocalExtension J z hJ).ker := by
    exact affineQuotientLocalExtension_ker_eq_span_of_span_eq J z hJ F hF
  have hker : (affineQuotientLocalExtension J z hJ).ker.FG := by
    rw [← hFlocal]
    exact Submodule.fg_span (Set.finite_range Flocal)
  have hambient : Module.finrank
      (ResidueField (AffineQuotientRationalPointLocalRing J z hJ))
      (ResidueField (AffineQuotientRationalPointLocalRing J z hJ)
        ⊗[AffineQuotientRationalPointLocalRing J z hJ]
          (affineQuotientLocalExtension J z hJ).CotangentSpace) = N := by
    simpa using
      (affineQuotientResidualAmbientCoordinates J z hJ).finrank_eq
  letI : IsLocalRing (affineQuotientLocalExtension J z hJ).Ring := by
    change IsLocalRing
      (Localization.AtPrime (affineEvaluationPrime z))
    infer_instance
  letI : Algebra.FormallySmooth k
      (affineQuotientLocalExtension J z hJ).Ring := by
    let R := MvPolynomial (Fin N) k
    let L := Localization.AtPrime (affineEvaluationPrime z)
    letI : Algebra.FormallySmooth R L :=
      Algebra.FormallySmooth.of_isLocalization
        (affineEvaluationPrime z).primeCompl
    change Algebra.FormallySmooth k L
    exact Algebra.FormallySmooth.comp k R L
  letI : Module.Free (affineQuotientLocalExtension J z hJ).Ring
      Ω[(affineQuotientLocalExtension J z hJ).Ring⁄k] := by
    change Module.Free
      (Localization.AtPrime (affineEvaluationPrime z))
      Ω[Localization.AtPrime (affineEvaluationPrime z)⁄k]
    exact Module.Free.of_basis (affinePolynomialLocalKaehlerBasis z)
  letI : Module.Finite (affineQuotientLocalExtension J z hJ).Ring
      Ω[(affineQuotientLocalExtension J z hJ).Ring⁄k] := by
    change Module.Finite
      (Localization.AtPrime (affineEvaluationPrime z))
      Ω[Localization.AtPrime (affineEvaluationPrime z)⁄k]
    exact Module.Finite.of_basis (affinePolynomialLocalKaehlerBasis z)
  obtain ⟨rows, cols, hrows, hcols, hminor, hgenerate⟩ :=
    exists_selected_localKernel_generators_and_minor
      (affineQuotientLocalExtension J z hJ) hker hambient htarget Flocal hFlocal
        (affineQuotientResidualAmbientCoordinates J z hJ)
  refine ⟨rows, cols, hrows, hcols, ?_, ?_⟩
  · simpa only [Flocal, affineQuotientLocalKernelElement] using hminor
  · simpa only [Flocal] using hgenerate

/-- Literal polynomial form of the preceding selection theorem.  The
selected equations generate the exact localized ideal, and their ordinary
selected Jacobian determinant has nonzero evaluation in the ground field. -/
theorem exists_selected_affineIdeal_generators_and_literal_minor
    {k : Type u} [Field k] {N n s : ℕ}
    (J : Ideal (MvPolynomial (Fin N) k)) (z : Fin N → k)
    (hJ : J ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom)
    [Algebra.FormallySmooth k
      (AffineQuotientRationalPointLocalRing J z hJ)]
    (htarget : Module.finrank
      (ResidueField (AffineQuotientRationalPointLocalRing J z hJ))
      (ResidueField (AffineQuotientRationalPointLocalRing J z hJ)
        ⊗[AffineQuotientRationalPointLocalRing J z hJ]
          Ω[AffineQuotientRationalPointLocalRing J z hJ⁄k]) = s)
    (F : Fin n → MvPolynomial (Fin N) k)
    (hF : Ideal.span (Set.range F) = J) :
    ∃ rows : Fin (N - s) → Fin n,
      ∃ cols : Fin (N - s) → Fin N,
        Function.Injective rows ∧ Function.Injective cols ∧
          MvPolynomial.eval z
            (selectedJacobianDeterminant (fun i ↦ F (rows i)) cols) ≠ 0 ∧
          Ideal.span (Set.range fun i ↦
            algebraMap (MvPolynomial (Fin N) k)
              (Localization.AtPrime (affineEvaluationPrime z))
                (F (rows i))) =
            (affineQuotientLocalExtension J z hJ).ker := by
  classical
  obtain ⟨rows, cols, hrows, hcols, hminor, hgenerate⟩ :=
    exists_selected_affineIdeal_generators_and_residual_minor
      J z hJ htarget F hF
  let S := AffineQuotientRationalPointLocalRing J z hJ
  let κ := ResidueField S
  let e : κ ≃ₐ[k] k :=
    affineQuotientRationalPointResidueFieldAlgEquiv J z hJ
  let M : Matrix (Fin (N - s)) (Fin (N - s)) κ :=
    Matrix.of (fun i j ↦
      affineQuotientResidualAmbientCoordinates J z hJ
        (((affineQuotientLocalExtension J z hJ).cotangentComplex.baseChange κ)
          ((1 : κ) ⊗ₜ[S]
            Algebra.Extension.Cotangent.mk
              (affineQuotientLocalKernelElement J z hJ
                (F (rows i)) (hF.le
                  (Ideal.subset_span ⟨rows i, rfl⟩)))))
        (cols j))
  let B : Matrix (Fin (N - s)) (Fin (N - s)) k :=
    Matrix.of (fun i j ↦
      MvPolynomial.eval z (MvPolynomial.pderiv (cols j) (F (rows i))))
  let C : Matrix (Fin (N - s)) (Fin (N - s)) k :=
    Matrix.of (fun i j ↦
      MvPolynomial.eval z (MvPolynomial.pderiv (cols i) (F (rows j))))
  have hM : M.det ≠ 0 := by
    simpa only [M, S, κ] using hminor
  have heM : e M.det ≠ 0 := by
    intro hz0
    apply hM
    apply e.injective
    simpa only [map_zero] using hz0
  have hmapMatrix : e.toRingHom.mapMatrix M = B := by
    ext i j
    exact affineQuotientResidualAmbientCoordinate_equiv_eq_eval_pderiv
      J z hJ (F (rows i))
        (hF.le (Ideal.subset_span ⟨rows i, rfl⟩)) (cols j)
  have hB : B.det ≠ 0 := by
    rw [← hmapMatrix, ← e.toRingHom.map_det]
    exact heM
  have hBC : B = C.transpose := by
    ext i j
    rfl
  have hC : C.det ≠ 0 := by
    rw [← Matrix.det_transpose C, ← hBC]
    exact hB
  refine ⟨rows, cols, hrows, hcols, ?_, hgenerate⟩
  rw [selectedJacobianDeterminant,
    (MvPolynomial.eval z).map_det]
  simpa only [C, RingHom.mapMatrix_apply, Matrix.of_apply] using hC

end

end TranslatedDepthSeven
