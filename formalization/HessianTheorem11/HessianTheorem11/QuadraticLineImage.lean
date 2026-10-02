import HessianTheorem11.KernelQuadraticDominance

/-! A quadratic image of affine dimension at most one spans at most one
vector dimension. This supplies dominance for two independent quadrics. -/
noncomputable section
namespace HessianTheorem11
open MvPolynomial Matrix Module PolynomialRestriction
variable {n m : ℕ}

theorem quadratic_low_image_span_le_one
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (Q : Fin m → GeometricPolynomial n) (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (hdim : affineDimension (geometricClosure (polynomialMap Q '' Set.univ)) ≤ 1) :
    finrank GeometricField (Submodule.span GeometricField (polynomialMap Q '' Set.univ)) ≤ 1 := by
  classical
  by_cases hne : ∃ j, Q j ≠ 0
  · obtain ⟨G⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
      Q (quadraticJacobianLinearMap Q hQ)
    obtain ⟨j, hj⟩ := hne
    obtain ⟨x, hx, hxQ⟩ := G.exists_polynomial_ne_zero (Q j) hj
    have hGdim : G.imageDimension ≤ 1 := by rw [G.dimension_image] at hdim; exact_mod_cast hdim
    have hxJ : (quadraticJacobianLinearMap Q hQ x).mulVec x ≠ 0 := by
      rw [quadraticJacobian_mulVec_self]
      intro he
      have hh : 2 * eval x (Q j) = 0 := by
        simpa [polynomialMap, nsmul_eq_mul] using congrFun he j
      exact hxQ ((mul_eq_zero.mp hh).resolve_left (by norm_num))
    let B : Matrix (Fin n) (Fin 1) GeometricField := fun i _ => x i
    have hb (a : GeometricPoint 1) : B.mulVec a = a 0 • x := by
      ext i
      simp [B, Matrix.mulVec, dotProduct, mul_comm]
    let R : Fin m → GeometricPolynomial 1 := fun i => restrict B (Q i)
    have hR : ∀ i, (R i).IsHomogeneous 2 := fun i => homogeneous_restrict B (Q i) (hQ i)
    obtain ⟨H⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
      R (quadraticJacobianLinearMap R hR)
    have hHdim : G.imageDimension ≤ H.imageDimension := by
      have hh := H.quadratic_rank_le (![1] : GeometricPoint 1)
      rw [quadraticJacobian_restrict Q hQ B, hb] at hh
      simp only [Matrix.cons_val_zero, one_smul] at hh
      have hi : Function.Injective (quadraticJacobianLinearMap Q hQ x * B).mulVec := by
        rw [Matrix.mulVec_injective_iff]
        apply LinearIndependent.of_subsingleton 0
        intro hz
        apply hxJ
        have he : (quadraticJacobianLinearMap Q hQ x * B).col 0 =
            (quadraticJacobianLinearMap Q hQ x).mulVec x := rfl
        rwa [he] at hz
      have hr := LinearMap.finrank_range_of_inj
        (f := (quadraticJacobianLinearMap Q hQ x * B).mulVecLin) hi
      have hr : (quadraticJacobianLinearMap Q hQ x * B).rank = 1 := by simpa using hr
      rw [hr] at hh
      omega
    have hsub : geometricClosure (polynomialMap R '' Set.univ) ⊆
        geometricClosure (polynomialMap Q '' Set.univ) := by
      apply geometricClosure_mono
      rintro _ ⟨a, _, rfl⟩
      refine ⟨B.mulVec a, Set.mem_univ _, ?_⟩
      ext i
      exact (eval_restrict B (Q i) a).symm
    have heq : geometricClosure (polynomialMap R '' Set.univ) =
        geometricClosure (polynomialMap Q '' Set.univ) := by
      by_contra hne
      have hlt := AD.proper_closed _ _ (algebraicallyClosedSet_geometricClosure _)
        (algebraicallyClosedSet_geometricClosure _)
        ((geometricallyIrreducible_closure_iff _).mpr
          (geometricallyIrreducible_univ.polynomialMap_image Q))
        (Set.ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩)
      rw [H.dimension_image, G.dimension_image] at hlt
      have hh : H.imageDimension < G.imageDimension := by exact_mod_cast hlt
      omega
    let S := Submodule.span GeometricField ({polynomialMap Q x} : Set (GeometricPoint m))
    have hsmall : polynomialMap R '' Set.univ ⊆ S := by
      rintro _ ⟨a, _, rfl⟩
      have he : polynomialMap R a = (a 0)^2 • polynomialMap Q x := by
        ext i
        change eval a (restrict B (Q i)) = ((a 0)^2 • polynomialMap Q x) i
        rw [eval_restrict, hb]
        simpa using quadratic_eval_two_vector_expansion (Q i) (hQ i) x 0 (a 0) 0
      rw [he]
      exact S.smul_mem _ (Submodule.mem_span_singleton_self _)
    have hcl := geometricClosure_subset_closed hsmall (algebraicallyClosedSet_submodule S)
    rw [heq] at hcl
    have hs := Submodule.finrank_mono (Submodule.span_le.mpr
      ((subset_geometricClosure _).trans hcl))
    have hb : finrank GeometricField S ≤ 1 := finrank_span_le_card ({polynomialMap Q x} : Set _)
    exact hs.trans hb
  · push_neg at hne
    have hs : Submodule.span GeometricField (polynomialMap Q '' Set.univ) = ⊥ := by
      apply le_antisymm _ bot_le
      apply Submodule.span_le.mpr
      rintro _ ⟨x, _, rfl⟩
      change polynomialMap Q x = 0
      ext j
      simp [polynomialMap, hne j]
    rw [hs]
    simp

theorem two_independent_quadrics_dense
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (Q : Fin 2 → GeometricPolynomial n) (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (hli : LinearIndependent GeometricField Q) :
    geometricClosure (polynomialMap Q '' Set.univ) = Set.univ := by
  by_contra hne
  have hlt := AD.proper_closed _ Set.univ (algebraicallyClosedSet_geometricClosure _)
    algebraicallyClosedSet_univ geometricallyIrreducible_univ
    (Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, hne⟩)
  rw [affineDimension_univ_from_generic_rank GR 2] at hlt
  obtain ⟨G⟩ := GR.choose Set.univ algebraicallyClosedSet_univ geometricallyIrreducible_univ
    Q (quadraticJacobianLinearMap Q hQ)
  have hd : G.imageDimension < 2 := by rw [G.dimension_image] at hlt; exact_mod_cast hlt
  have hb := quadratic_low_image_span_le_one GR AD Q hQ (by
    rw [G.dimension_image]
    have hn : G.imageDimension ≤ 1 := by omega
    exact_mod_cast hn)
  let S := Submodule.span GeometricField (polynomialMap Q '' Set.univ)
  have hsmall : finrank GeometricField S ≤ 1 := hb
  let a := finrank GeometricField S
  obtain ⟨D⟩ := exists_polynomialImageCoordinates Q (show finrank GeometricField S = a from rfl)
  have hsp := span_combinePolynomials_le
    (fun i j => D.embedding ((Pi.basisFun GeometricField (Fin a)) j) i) D.tuple
  have he : Q = combinePolynomials
      (fun i j => D.embedding ((Pi.basisFun GeometricField (Fin a)) j) i) D.tuple := D.reconstruct
  rw [← he] at hsp
  letI : Module.Finite GeometricField
      (Submodule.span GeometricField (Set.range D.tuple)) :=
    Module.Finite.span_of_finite GeometricField (Set.finite_range D.tuple)
  have hr := Submodule.finrank_mono hsp
  rw [finrank_span_eq_card hli] at hr
  have hu := finrank_range_le_card (R := GeometricField) D.tuple
  simp only [Fintype.card_fin] at hr hu
  change finrank GeometricField (Submodule.span GeometricField (Set.range D.tuple)) ≤ a at hu
  have htwo : 2 ≤ a := hr.trans hu
  omega

theorem quadratic_imageClosure_eq_span_of_span_finrank_two
    (GR : GenericRankOpenInput) (AD : AffineHypersurfaceDimensionInput)
    (Q : Fin m → GeometricPolynomial n) (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (hdim : finrank GeometricField (Submodule.span GeometricField
      (polynomialMap Q '' Set.univ)) = 2) :
    geometricClosure (polynomialMap Q '' Set.univ) =
      (Submodule.span GeometricField (polynomialMap Q '' Set.univ) : Set (GeometricPoint m)) := by
  obtain ⟨D⟩ := exists_polynomialImageCoordinates Q hdim
  exact D.imageClosure_eq_span_of_dense
    (two_independent_quadrics_dense GR AD D.tuple (D.homogeneous hQ) D.independent)

end HessianTheorem11
