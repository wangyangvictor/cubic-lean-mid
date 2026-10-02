import TranslatedDepthSeven.ProjectiveDegreeSpanGenericExtension
import TranslatedDepthSeven.ProjectiveDegreeSpanSectionReduction

/-!
# Degree--span from integral sections over successively larger fields

A hyperplane section need not be specialized back to the original field.
The geometric existence hypothesis below allows passing to an arbitrary
algebraically closed extension at every induction step. Exact scalar
extension of Hilbert pieces and the internally proved dimension--degree
transfer make the numerical inequality descend at each step.

The section-existence statement remains an explicit hypothesis here.
No generic-section construction, Bertini theorem, or input removal is
claimed by this file. All coefficient fields remain in one universe;
rational-function fields and their algebraic closures have this property.
-/

namespace TranslatedDepthSeven

universe u

noncomputable section

open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- A purely geometric integral-section statement, allowing a new
algebraically closed coefficient field at each step. Primality of the
extended source is included explicitly. The section is represented by a
nonempty homogeneous prime chart-saturation of a proper linear section.
There are no degree, Hilbert-polynomial, or linear-span conclusions. -/
def ProjectiveGenericIntegralHyperplaneSectionExists : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
    (N r : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) K)),
    2 ≤ r → I.IsPrime →
    I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) →
    ringKrullDim (MvPolynomial (Fin (N + 1)) K ⧸ I) = r + 1 →
    ∃ (L : Type u) (hLfield : Field L),
      letI : Field L := hLfield
      ∃ hLalgebra : Algebra K L,
        letI : Algebra K L := hLalgebra
        IsAlgClosed L ∧
        (I.map (MvPolynomial.map (algebraMap K L))).IsPrime ∧
        ∃ (ℓ : MvPolynomial (Fin (N + 1)) L)
          (J : Ideal (MvPolynomial (Fin (N + 1)) L)),
          ℓ.IsHomogeneous 1 ∧
          ℓ ∉ I.map (MvPolynomial.map (algebraMap K L)) ∧
          J.IsPrime ∧
          J.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) L) ∧
          (∃ i : Fin (N + 1), X i ∉ J) ∧
          I.map (MvPolynomial.map (algebraMap K L)) ⊔
              Ideal.span ({ℓ} : Set _) ≤ J ∧
          ∀ (F : MvPolynomial (Fin (N + 1)) L), F ∈ J →
            ∀ i : Fin (N + 1),
            ∃ k : ℕ, (X i : MvPolynomial (Fin (N + 1)) L) ^ k * F ∈
              I.map (MvPolynomial.map (algebraMap K L)) ⊔
                Ideal.span ({ℓ} : Set _)

/-- A changing-field induction: each proper section can be taken over a
larger algebraically closed field without any specialization theorem. -/
theorem projectiveDegreeSpan_hilbertOne_of_genericIntegralHyperplaneSections
    (sections : ProjectiveGenericIntegralHyperplaneSectionExists.{u})
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    {N r d : ℕ} (I : Ideal (MvPolynomial (Fin (N + 1)) K))
    (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (hdegree : HasProjectiveDimensionDegree I r d) :
    Module.finrank K (projectiveHilbertPiece K N I 1) ≤ r + d := by
  have hbound : ∀ r : ℕ, ∀ (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
      (N d : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) K)),
      I.IsPrime →
      I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K) →
      HasProjectiveDimensionDegree I r d →
      Module.finrank K (projectiveHilbertPiece K N I 1) ≤ r + d := by
    intro r
    induction r with
    | zero =>
      intro K _ _ _ N d I hI hhom hdegree
      simpa only [Nat.zero_add] using
        projectiveSection_zerofold_hilbertOne_le_degree I hI hhom hdegree
    | succ r ih =>
      intro K _ _ _ N d I hI hhom hdegree
      by_cases hr : r = 0
      · subst r
        simpa only [Nat.add_comm d 1] using
          projectiveCurve_hilbertOne_le_degree_add_one I hI hhom hdegree
      · obtain ⟨L, hLfield, hLdata⟩ :=
          sections K N (r + 1) I (by omega) hI hhom hdegree.1
        letI : Field L := hLfield
        obtain ⟨hLalgebra, hLdata⟩ := hLdata
        letI : Algebra K L := hLalgebra
        obtain ⟨hLclosed, hIext, ℓ, J, hℓhom, hℓ, hJ, hJhom,
          hchart, hle, hsat⟩ := hLdata
        letI : IsAlgClosed L := hLclosed
        letI : CharZero L :=
          charZero_of_injective_algebraMap (algebraMap K L).injective
        let Iext := I.map (MvPolynomial.map (algebraMap K L))
        have hhomext : Iext.IsHomogeneous
            (homogeneousSubmodule (Fin (N + 1)) L) :=
          isHomogeneous_map_mvPolynomialMap (algebraMap K L) I hhom
        have hdegreeext : HasProjectiveDimensionDegree Iext (r + 1) d :=
          hasProjectiveDimensionDegree_coefficientExtension I hhom hdegree hIext
        obtain ⟨e, hed, hJdegree⟩ := projectiveSection_saturatedPrime_dimension_degree
          Iext J hIext hdegreeext ℓ hℓhom hℓ hJ hJhom hchart hle hsat
        have hnext := ih L N e J hJ hJhom hJdegree
        have hdrop := projectiveSection_saturation_hilbertOne_add_one
          Iext J hIext hhomext ℓ hℓhom hℓ hle hsat
        have hscalar := projectiveHilbertPiece_finrank_map_eq
          (K := K) (L := L) N 1 I
        change Module.finrank L (projectiveHilbertPiece L N Iext 1) =
          Module.finrank K (projectiveHilbertPiece K N I 1) at hscalar
        omega
  exact hbound r K N d I hI hhom hdegree

/-- The rational degree--span interface from the changing-field geometric
section hypothesis. The final descent is equality of linear-piece ranks. -/
theorem rationalProjectiveDegreeSpan_of_genericIntegralHyperplaneSections
    (sections : ProjectiveGenericIntegralHyperplaneSectionExists.{0}) :
    StandardAG.ProjectiveDegreeSpanInequality ℚ := by
  intro N r d I hI hgeometric hhom hdegree
  apply projectiveDegreeSpan_descends_coefficientExtension (L := Qbar)
  let Ibar := I.map (MvPolynomial.map (algebraMap ℚ Qbar))
  have hbound := projectiveDegreeSpan_hilbertOne_of_genericIntegralHyperplaneSections
    sections Ibar hgeometric
    (isHomogeneous_map_mvPolynomialMap (algebraMap ℚ Qbar) I hhom)
    (hasProjectiveDimensionDegree_coefficientExtension I hhom hdegree hgeometric)
  have hsum := finrank_degreeOnePart_add_quotientHomogeneousComponent_eq Ibar
  change Module.finrank Qbar
    (quotientHomogeneousComponent Qbar (Fin (N + 1)) Ibar 1) ≤ r + d at hbound
  change N + 1 ≤ Module.finrank Qbar (StandardAG.degreeOnePartInIdeal Ibar) + r + d
  omega

end

end TranslatedDepthSeven
