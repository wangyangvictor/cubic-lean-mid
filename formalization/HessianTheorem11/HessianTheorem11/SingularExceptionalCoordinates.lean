import HessianTheorem11.SingularExceptionalComponent
import HessianTheorem11.SingularTwelveReduction
import HessianTheorem11.SingularRankFourWitness

/-! Actual adapted coordinates and normal quadrics on the exceptional
rank-five components selected from a violation of the singular bound. -/
noncomputable section
namespace HessianTheorem11.SingularRankFiveException
open Module MvPolynomial SingularRadialNormalForm SingularPositiveNormalForm
open SingularRadialEquality NonzeroLimitTransport PolynomialRestriction
variable {n : ℕ} {F : AnisotropicCubic n}

theorem tensor (E : SingularRankFiveException F) (DT : SymmetricDeterminantalTangentInput)
    (x : GeometricPoint n) (hx : x ∈ E.generic.openSet) :
    ∀ t ∈ affineTangentSpace E.base x,
      ∀ u ∈ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
      ∀ v ∈ LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin,
        polarization (geometricPolynomial F.polynomial) t u v = 0 :=
  hessian_tangent_polarization_zero DT _ (geometric_homogeneous F.homogeneous)
    E.base x (E.generic.subset hx) (E.generic.maximal_rank x hx)

theorem adapted_basis (E : SingularRankFiveException F)
    (x : GeometricPoint n) (hx : x ∈ E.generic.openSet) :
    Nonempty (AdaptedFlagBasis (affineTangentSpace E.base x)
      (LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin) x) :=
  nonempty_adaptedFlagBasis _ _ (affineTangentSpace_le_hessian_ker _ E.base E.singular x)
    x (E.point_nonzero x hx) (E.radial x hx)

theorem graded_coordinates (E : SingularRankFiveException F) (hn : 5 ≤ n)
    (x : GeometricPoint n) (hx : x ∈ E.generic.openSet)
    (A : AdaptedFlagBasis (affineTangentSpace E.base x)
      (LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin) x) :
    Nonempty (GradedIndexCoordinates A.tangentIndices A.radial 5 (n-6)) := by
  classical
  apply GradedIndexCoordinates.exists_coordinates _ _ A.radial_mem
  · rw [Finset.card_compl, Fintype.card_fin, A.tangent_card, E.tangent_dimension x hx]
    omega
  · rw [Finset.card_erase_of_mem A.radial_mem, A.tangent_card, E.tangent_dimension x hx]
    omega

theorem normal_data (E : SingularRankFiveException F) (DT : SymmetricDeterminantalTangentInput)
    (hn : 5 ≤ n) (x : GeometricPoint n) (hx : x ∈ E.generic.openSet)
    (A : AdaptedFlagBasis (affineTangentSpace E.base x)
      (LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin) x) :
    ∃ q : MvPolynomial (↑A.tangentIndicesᶜ : Type) GeometricField,
    ∃ p : (↑A.tangentIndicesᶜ : Type) →
      MvPolynomial (↑(A.tangentIndices.erase A.radial) : Type) GeometricField,
    q.IsHomogeneous 2 ∧ (∀ i, (p i).IsHomogeneous 2) ∧
    rename (fun i : (↑A.tangentIndicesᶜ : Type) => (i : Fin n)) q =
      normalQuadratic (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis)
        (geometricPolynomial F.polynomial))
        (singularRadialWeight A.radial A.tangentIndices A.tangentIndices)) A.radial ∧
    (∀ i, rename (fun j : (↑(A.tangentIndices.erase A.radial) : Type) => (j : Fin n)) (p i) =
      normalMapComponent (zeroWeightPart (restrict (HessianTheorem11.basisMatrix A.basis)
        (geometricPolynomial F.polynomial))
        (singularRadialWeight A.radial A.tangentIndices A.tangentIndices))
        A.radial A.tangentIndices i) := by
  have hw := nonnegative_in_adapted_flag _ (geometric_homogeneous F.homogeneous) x
    (affineTangentSpace E.base x) A (E.tensor DT x hx)
  have he := adapted_indices_eq_of_tangent_eq_kernel _ x _ A (E.tangent_eq_kernel hn x hx)
  rw [← he] at hw
  obtain ⟨q,p,hq,hp,hqe,hpe,_⟩ := exists_typed_positive_normal_form
    (restrict (HessianTheorem11.basisMatrix A.basis) (geometricPolynomial F.polynomial))
    (homogeneous_restrict _ _ (geometric_homogeneous F.homogeneous)) A.radial A.tangentIndices A.radial_mem hw
  exact ⟨q,p,hq,hp,hqe,hpe⟩

theorem twelve_equality_data {F : AnisotropicCubic 12}
    (E : SingularRankFiveException F) (DT : SymmetricDeterminantalTangentInput)
    (boundary : RationalRelativeBoundaryInput) (bigCell : TextbookOrbitBigCellInput)
    (hirred : Irreducible (geometricPolynomial F.polynomial))
    (hdet : hessianDeterminantPolynomial (geometricPolynomial F.polynomial) ≠ 0)
    (x : GeometricPoint 12) (hx : x ∈ E.generic.openSet) :
    Nonempty (EqualityData 5 (geometricPolynomial F.polynomial) x (affineTangentSpace E.base x)) := by
  apply nonempty_equalityData boundary bigCell F (by norm_num) 5 hirred hdet x
    (E.point_nonzero x hx) _ (E.radial x hx)
    (affineTangentSpace_le_hessian_ker _ E.base E.singular x) (E.tensor DT x hx)
  · rw [E.tangent_dimension x hx]
  · exact E.rank_five x hx

end HessianTheorem11.SingularRankFiveException
