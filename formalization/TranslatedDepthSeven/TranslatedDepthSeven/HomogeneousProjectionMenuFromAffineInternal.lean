import TranslatedDepthSeven.HomogeneousProjectionEquivalenceInternal
import TranslatedDepthSeven.ProjectiveConeHilbertShift

/-!
# The homogeneous projection menu follows from the affine-chart menu

A homogeneous ideal avoiding the irrelevant ideal has a coordinate not in
the ideal.  Interchange it with coordinate zero, apply the affine-chart
menu, and interchange the source columns back.  The union over the finitely
many coordinate interchanges is selected before the source ideal.
-/

namespace TranslatedDepthSeven

noncomputable section

open MvPolynomial Published StandardAG

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

/-- Geometric primality is invariant under a permutation of coordinates:
the permutation commutes with every coefficient-field extension. -/
theorem geometricallyPrime_map_renameEquiv
    {N : ℕ} (e : Equiv.Perm (Fin N))
    (I : Ideal (MvPolynomial (Fin N) ℚ))
    (hI : GeometricallyPrimeMvPolynomialIdeal I) :
    GeometricallyPrimeMvPolynomialIdeal (I.map (renameEquiv ℚ e)) := by
  intro L _ _
  have heq :
      (I.map (renameEquiv ℚ e)).map (MvPolynomial.map (algebraMap ℚ L)) =
        (I.map (MvPolynomial.map (algebraMap ℚ L))).map (renameEquiv L e) := by
    change (I.map (renameEquiv ℚ e).toRingHom).map
        (MvPolynomial.map (algebraMap ℚ L)) =
      (I.map (MvPolynomial.map (algebraMap ℚ L))).map (renameEquiv L e).toRingHom
    rw [Ideal.map_map, Ideal.map_map]
    apply congrArg (fun f : MvPolynomial (Fin N) ℚ →+* MvPolynomial (Fin N) L ↦ I.map f)
    apply RingHom.ext
    intro f
    exact MvPolynomial.map_rename (algebraMap ℚ L) e f
  rw [heq]
  letI : (I.map (MvPolynomial.map (algebraMap ℚ L))).IsPrime := hI L
  exact Ideal.map_isPrime_of_equiv (renameEquiv L e).toRingEquiv

/-- Both the quotient Krull dimension and every homogeneous Hilbert piece
are preserved by a coordinate permutation. -/
theorem hasProjectiveDimensionDegree_map_renameEquiv
    {N r d : ℕ} (e : Equiv.Perm (Fin (N + 1)))
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ))
    (hI : HasProjectiveDimensionDegree I r d) :
    HasProjectiveDimensionDegree (I.map (renameEquiv ℚ e)) r d := by
  rcases hI with ⟨hdim, hd, P, hPdegree, hPlc, k₀, heventual⟩
  refine ⟨?_, hd, P, hPdegree, hPlc, k₀, ?_⟩
  · rw [← ringKrullDim_eq_of_ringEquiv (renameQuotientAlgEquiv ℚ e I).toRingEquiv]
    exact hdim
  · intro k hk
    have heq := finrank_quotientHomogeneousComponent_map_renameEquiv ℚ e I k
    change Module.finrank ℚ (projectiveHilbertPiece ℚ N I k) =
      Module.finrank ℚ
        (projectiveHilbertPiece ℚ N (I.map (renameEquiv ℚ e)) k) at heq
    rw [← heq]
    exact heventual k hk

/-- The inverse coordinate permutation acts on a linear form by permuting
the columns of its coefficient row in the opposite direction. -/
theorem renameEquiv_symm_projectiveMatrixLinearForm
    {c N : ℕ} (e : Equiv.Perm (Fin N))
    (A : Matrix (Fin c) (Fin N) ℚ) (i : Fin c) :
    (renameEquiv ℚ e).symm (projectiveMatrixLinearForm A i) =
      projectiveMatrixLinearForm (fun k j ↦ A k (e j)) i := by
  simp only [projectiveMatrixLinearForm, map_sum, map_mul,
    renameEquiv_symm, renameEquiv_apply, rename_C, rename_X]
  simpa using (Equiv.sum_comp e
    (fun j ↦ C (A i j) * X (e.symm j))).symm

/-- Return a projection of the renamed ideal to the original source.
The equation, finite-ring-map condition, fraction degree, and every
geometric fibre bound are all retained. -/
theorem isHomogeneousFiniteBirationalLinearProjection_of_renameEquiv
    {N r d : ℕ} (e : Equiv.Perm (Fin (N + 1)))
    (I : Ideal (MvPolynomial (Fin (N + 1)) ℚ)) (hI : I.IsPrime)
    (hJ : (I.map (renameEquiv ℚ e)).IsPrime)
    (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ)
    (G : MvPolynomial (Fin (r + 2)) ℚ)
    (hp : IsHomogeneousFiniteBirationalLinearProjection (degree := d)
      (I.map (renameEquiv ℚ e)) hJ A G) :
    IsHomogeneousFiniteBirationalLinearProjection (degree := d)
      I hI (fun k j ↦ A k (e j)) G := by
  let J := I.map (renameEquiv ℚ e)
  let E := renameQuotientAlgEquiv ℚ e I
  have hEmk (f : MvPolynomial (Fin (N + 1)) ℚ) :
      E (Ideal.Quotient.mk I f) = Ideal.Quotient.mk J (renameEquiv ℚ e f) :=
    Ideal.quotientEquivAlg_mk _ (renameEquiv ℚ e) rfl f
  have hEback (f : MvPolynomial (Fin (N + 1)) ℚ) :
      E.symm (Ideal.Quotient.mk J f) =
        Ideal.Quotient.mk I ((renameEquiv ℚ e).symm f) := by
    apply E.injective
    rw [E.apply_symm_apply, hEmk, AlgEquiv.apply_symm_apply]
  apply isHomogeneousFiniteBirationalLinearProjection_of_source_equiv
    J I hJ hI A (fun k j ↦ A k (e j)) G E.symm _ hp
  apply MvPolynomial.algHom_ext
  intro i
  change E.symm
      (Ideal.Quotient.mk J (MvPolynomial.aeval (projectiveMatrixLinearForm A) (X i))) =
    Ideal.Quotient.mk I
      (MvPolynomial.aeval (projectiveMatrixLinearForm (fun k j ↦ A k (e j))) (X i))
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X, hEback,
    renameEquiv_symm_projectiveMatrixLinearForm]

/-- The homogeneous finite menu is a consequence, not a second independent
geometric input.  The finite union is over coordinate interchanges chosen
before the ideal and its degree. -/
theorem boundedDegreeHomogeneousProjectionMenu_of_affineChart
    (hAffine : BoundedDegreeAffineChartProjectionMenu) :
    BoundedDegreeHomogeneousProjectionMenu := by
  classical
  intro N r D hr
  obtain ⟨menu, hmenu⟩ := hAffine N r D hr
  let e (j : Fin (N + 1)) := Equiv.swap (0 : Fin (N + 1)) j
  let matrix (j : Fin (N + 1))
      (A : Matrix (Fin (r + 2)) (Fin (N + 1)) ℤ) :
      Matrix (Fin (r + 2)) (Fin (N + 1)) ℚ :=
    fun row col ↦ (A row (e j col) : ℚ)
  refine ⟨Finset.univ.biUnion (fun j ↦ menu.image (matrix j)), ?_⟩
  intro I hI hgeom hhom hirrel d hdim hd
  have hexists : ∃ j : Fin (N + 1), X j ∉ I := by
    by_contra h
    push_neg at h
    apply hirrel
    rw [projectiveIrrelevantIdeal, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact h j
  obtain ⟨j, hj⟩ := hexists
  let J := I.map (renameEquiv ℚ (e j))
  letI : I.IsPrime := hI
  have hJ : J.IsPrime := Ideal.map_isPrime_of_equiv (renameEquiv ℚ (e j)).toRingEquiv
  have hJgeom : GeometricallyPrimeMvPolynomialIdeal J :=
    geometricallyPrime_map_renameEquiv (e j) I hgeom
  have hJhom : J.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) ℚ) :=
    map_renameEquiv_isHomogeneous (e j) I hhom
  have hJzero : X (0 : Fin (N + 1)) ∉ J := by
    intro hz
    have hback : (renameEquiv ℚ (e j)).symm (X (0 : Fin (N + 1))) ∈ I :=
      (Ideal.symm_apply_mem_of_equiv_iff
        (f := (renameEquiv ℚ (e j)).toRingEquiv)).mpr hz
    apply hj
    simpa [e, renameEquiv_symm, renameEquiv_apply] using hback
  obtain ⟨A, hA, G, hproj, _himage⟩ := hmenu J hJ hJgeom hJhom hJzero d
    (hasProjectiveDimensionDegree_map_renameEquiv (e j) I hdim) hd
  refine ⟨matrix j A, Finset.mem_biUnion.mpr
    ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨A, hA, rfl⟩⟩, G, ?_⟩
  exact isHomogeneousFiniteBirationalLinearProjection_of_renameEquiv
    (e j) I hI hJ (A.map (Int.castRingHom ℚ)) G hproj.2

end

end TranslatedDepthSeven
