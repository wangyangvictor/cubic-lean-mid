import TranslatedDepthSeven.AugmentedNormalizationHypersurfaceKernelInternal
import TranslatedDepthSeven.PrincipalHomogeneousHypersurfaceDegreeInternal

/-!
# The augmented kernel with its exact minimal-polynomial degree

The generator is the minimal polynomial itself after reindexing. An
equality for its degree is therefore retained in the conclusion. The
principal hypersurface Hilbert calculation supplies the image's exact
projective degree, independently of any degree upper-bound argument.
The last lemma permits arbitrary target coordinate permutations, in
particular moving the retained original first coordinate back to position
zero after adjoining the primitive coordinate.
-/

namespace TranslatedDepthSeven
noncomputable section
open MvPolynomial Published
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000

theorem augmentedLinearNormalization_exists_kernel_of_minpoly_degree
    {K : Type*} [Field K] [CharZero K] {N d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (D : HomogeneousLinearNormalizationData I)
    (w : MvPolynomial (Fin (N + 1)) K) (hwhom : w.IsHomogeneous 1)
    (hminpoly :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin (N + 1)) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      (minpoly B (Ideal.Quotient.mk I w)).natDegree = d) :
    ∃ G : MvPolynomial (Fin (D.parameterCount + 1)) K,
      (augmentedLinearNormalizationHom D (Ideal.Quotient.mk I w)).Finite ∧
      RingHom.ker (augmentedLinearNormalizationHom D (Ideal.Quotient.mk I w)).toRingHom =
        Ideal.span ({G} : Set _) ∧
      G.IsHomogeneous d ∧ Irreducible G := by
  classical
  letI : I.IsPrime := hIprime
  let B := MvPolynomial (Fin D.parameterCount) K
  let A := MvPolynomial (Fin (N + 1)) K ⧸ I
  letI : Algebra B A := D.hom.toRingHom.toAlgebra
  letI : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr D.hom_injective
  letI : Module.Finite B A := D.hom_finite
  let u : A := Ideal.Quotient.mk I w
  let p := minpoly B u
  let E := (renameEquiv K (_root_.finSuccEquiv D.parameterCount)).trans
    (optionEquivLeft K (Fin D.parameterCount))
  let G := E.symm p
  have hu : IsIntegral B u := Algebra.IsIntegral.isIntegral u
  have hpdegree : p.natDegree = d := hminpoly
  refine ⟨G, augmentedLinearNormalizationHom_finite D u, ?_, ?_, ?_⟩
  · have hmap := augmentedLinearNormalizationHom_eq_polynomialEvaluation D u
    change augmentedLinearNormalizationHom D u =
      ((Polynomial.aeval u).restrictScalars K).comp E.toAlgHom at hmap
    ext f
    rw [RingHom.mem_ker, hmap]
    change Polynomial.aeval u (E f) = 0 ↔ f ∈ Ideal.span ({G} : Set _)
    rw [minpoly.isIntegrallyClosed_dvd_iff hu, Ideal.mem_span_singleton]
    change p ∣ E f ↔ E.symm p ∣ f
    simpa only [AlgEquiv.apply_symm_apply] using
      (map_dvd_iff E (a := E.symm p) (b := f))
  · have hhom := minpoly_isHomogeneous_of_linearNormalization I hIprime hIhom D w hwhom
    change ((optionEquivLeft K (Fin D.parameterCount)).symm p).IsHomogeneous
      p.natDegree at hhom
    rw [← hpdegree]
    change (rename (_root_.finSuccEquiv D.parameterCount).symm
      ((optionEquivLeft K (Fin D.parameterCount)).symm p)).IsHomogeneous p.natDegree
    exact hhom.rename_isHomogeneous
  · exact (minpoly.irreducible hu).map E.symm

/-- Exact image certificate in the original augmented coordinate order.
The parameter count equality only identifies the ambient polynomial ring;
the image Hilbert degree follows from its actual principal equation. -/
theorem augmentedLinearNormalization_exists_kernel_and_exact_image_degree
    {K : Type*} [Field K] [CharZero K] {N r d : ℕ}
    (I : Ideal (MvPolynomial (Fin (N + 1)) K)) (hIprime : I.IsPrime)
    (hIhom : I.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) K))
    (D : HomogeneousLinearNormalizationData I) (hcount : D.parameterCount = r + 1)
    (w : MvPolynomial (Fin (N + 1)) K) (hwhom : w.IsHomogeneous 1) (hd : 0 < d)
    (hminpoly :
      let B := MvPolynomial (Fin D.parameterCount) K
      let A := MvPolynomial (Fin (N + 1)) K ⧸ I
      letI : Algebra B A := D.hom.toRingHom.toAlgebra
      (minpoly B (Ideal.Quotient.mk I w)).natDegree = d) :
    ∃ G : MvPolynomial (Fin (D.parameterCount + 1)) K,
      (augmentedLinearNormalizationHom D (Ideal.Quotient.mk I w)).Finite ∧
      RingHom.ker (augmentedLinearNormalizationHom D (Ideal.Quotient.mk I w)).toRingHom =
        Ideal.span ({G} : Set _) ∧
      G.IsHomogeneous d ∧ Irreducible G ∧
      HasProjectiveDimensionDegree
        (RingHom.ker (augmentedLinearNormalizationHom D (Ideal.Quotient.mk I w)).toRingHom)
        r d := by
  obtain ⟨G, hfinite, hker, hGhom, hGirreducible⟩ :=
    augmentedLinearNormalization_exists_kernel_of_minpoly_degree
      I hIprime hIhom D w hwhom hminpoly
  refine ⟨G, hfinite, hker, hGhom, hGirreducible, ?_⟩
  letI : I.IsPrime := hIprime
  have hprime : (Ideal.span ({G} : Set _)).IsPrime := by
    rw [← hker]
    exact RingHom.ker_isPrime _
  rw [hker]
  have hprincipal (m : ℕ) (hm : m = r + 1)
      (F : MvPolynomial (Fin (m + 1)) K) (hF : F.IsHomogeneous d)
      (hFne : F ≠ 0) (hFprime : (Ideal.span ({F} : Set _)).IsPrime) :
      HasProjectiveDimensionDegree (Ideal.span ({F} : Set _)) r d := by
    subst m
    exact hasProjectiveDimensionDegree_principal_homogeneous F hF hFne hd hFprime
  exact hprincipal D.parameterCount hcount G hGhom hGirreducible.ne_zero hprime

/-- Precomposing with a target permutation inverse-renames the generator.
All Hilbert data is unchanged. This statement includes swapping the first
two target coordinates and has no restrictions on the permutation. -/
theorem principal_kernel_and_projectiveDegree_precomp_rename
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] {N r d : ℕ}
    (h : MvPolynomial (Fin (N + 1)) K →ₐ[K] A)
    (G : MvPolynomial (Fin (N + 1)) K)
    (hker : RingHom.ker h.toRingHom = Ideal.span ({G} : Set _))
    (hGhom : G.IsHomogeneous d) (hGirreducible : Irreducible G)
    (hdegree : HasProjectiveDimensionDegree (RingHom.ker h.toRingHom) r d)
    (e : Fin (N + 1) ≃ Fin (N + 1)) :
    RingHom.ker (h.comp (renameEquiv K e).toAlgHom).toRingHom =
        Ideal.span ({rename e.symm G} : Set _) ∧
      (rename e.symm G).IsHomogeneous d ∧
      Irreducible (rename e.symm G) ∧
      HasProjectiveDimensionDegree
        (RingHom.ker (h.comp (renameEquiv K e).toAlgHom).toRingHom) r d := by
  let E := renameEquiv K e
  have hker' : RingHom.ker (h.comp E.toAlgHom).toRingHom =
      (RingHom.ker h.toRingHom).map (renameEquiv K e.symm) := by
    ext f
    rw [RingHom.mem_ker]
    change h (E f) = 0 ↔ _
    rw [← RingHom.mem_ker]
    change E f ∈ RingHom.ker h.toRingHom ↔
      f ∈ (RingHom.ker h.toRingHom).map E.symm.toRingEquiv
    exact Ideal.symm_apply_mem_of_equiv_iff
      (I := RingHom.ker h.toRingHom) (f := E.symm.toRingEquiv) (y := f)
  have hspan : (Ideal.span ({G} : Set (MvPolynomial (Fin (N + 1)) K))).map
      (renameEquiv K e.symm) = Ideal.span ({rename e.symm G} : Set _) := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton, renameEquiv_apply]
  refine ⟨hker'.trans (by rw [hker, hspan]), hGhom.rename_isHomogeneous, ?_, ?_⟩
  · exact hGirreducible.map (renameEquiv K e.symm)
  · rw [hker']
    exact hasProjectiveDimensionDegree_map_renameEquiv_internal e.symm _ hdegree

end
end TranslatedDepthSeven
