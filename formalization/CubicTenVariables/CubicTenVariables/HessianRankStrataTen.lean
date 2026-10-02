import CubicTenVariables.GeometryTen

/-! Actual geometric Hessian rank strata of an anisotropic rational cubic in
ten variables. These bounds are over the algebraic closure of the rationals;
they do not assert any reduction or point count over finite fields. -/

noncomputable section
namespace CubicTenVariables.Geometry
open HessianTheorem11 MvPolynomial Module

/-- The rank locus is closed because its defining matrix consists of the
actual second partial polynomials. -/
theorem hessianRankLocus_closed (F : AnisotropicCubic 10) (r : ℕ) :
    AlgebraicallyClosedSet (rankAtMostLocus F.polynomial r) := by
  exact BibleLowRank.polynomialMatrix_rank_locus_closed
    (hessianPolynomial (geometricPolynomial F.polynomial)) r

theorem origin_mem_hessianRankLocus (F : AnisotropicCubic 10) (r : ℕ) :
    0 ∈ rankAtMostLocus F.polynomial r := by
  have hz : 0 ∈ rankAtMostLocus F.polynomial 0 := by
    rw [rankAtMost_zero_locus F]
    exact Set.mem_singleton 0
  exact le_trans hz (Nat.zero_le r)

/-- The rank-zero locus is exactly the origin, with affine dimension zero. -/
theorem hessianRankZero (F : AnisotropicCubic 10) :
    rankAtMostLocus F.polynomial 0 = {0} ∧
      affineDimension (rankAtMostLocus F.polynomial 0) = 0 :=
  ⟨rankAtMost_zero_locus F, rank_zero_locus_dimension F⟩

/-- The actual full incidence bound gives the base-rank bound by taking
the kernel bundle over a maximal-dimensional rank-locus component. -/
theorem hessianRankLocus_dimension_le_rank_add_two
    (F : AnisotropicCubic 10) (r : ℕ) :
    affineDimension (rankAtMostLocus F.polynomial r) ≤ ((r + 2 : ℕ) : Dimension) := by
  classical
  let P := geometricPolynomial F.polynomial
  have hP : P.IsHomogeneous 3 := geometric_homogeneous F.homogeneous
  obtain ⟨Z, hZ, hdim⟩ := Unconditional.concentrationGeometry.maximal_dimension_component
    (rankAtMostLocus F.polynomial r) (hessianRankLocus_closed F r)
    ⟨0, origin_mem_hessianRankLocus F r⟩
  obtain ⟨G⟩ := Unconditional.genericRankOpen.choose Z hZ.closed hZ.irreducible
    (fun i : Fin 10 => pderiv i P) (hessianLinearMap P hP)
  have hbundle := Unconditional.concentrationGeometry.dimension
    (hessianLinearMap P hP) Z G.openSet hZ.closed hZ.irreducible
    G.isOpen G.dense G.baseDimension G.nullity G.dimension_base G.kernel_dimension
  have hsub := affineDimension_mono (kernelBundle_subset_cubicIncidence P hP G.openSet)
  rw [hbundle] at hsub
  have hinc : affineDimension (cubicIncidence P) ≤ (12 : Dimension) :=
    incidenceDimension_le_twelve F
  have hbn : G.baseDimension + G.nullity ≤ 12 := by
    exact_mod_cast hsub.trans hinc
  obtain ⟨x, hx⟩ := G.nonempty
  have hrank : (hessian P x).rank ≤ r := hZ.subset (G.subset hx)
  have hnull : finrank GeometricField (LinearMap.ker (hessian P x).mulVecLin) =
      G.nullity := G.kernel_dimension x hx
  have hrn := (hessian P x).mulVecLin.finrank_range_add_finrank_ker
  change (hessian P x).rank + _ = _ at hrn
  have hrn' : (hessian P x).rank + G.nullity = 10 := by simpa [hnull] using hrn
  have hbase : G.baseDimension ≤ r + 2 := by omega
  rw [← hdim, G.dimension_base]
  exact_mod_cast hbase

/-- The actual geometric Hessian has a point of full rank. -/
theorem exists_geometric_hessian_full_rank (F : AnisotropicCubic 10) :
    ∃ x : GeometricPoint 10,
      (hessian (geometricPolynomial F.polynomial) x).rank = 10 := by
  classical
  have hdet := geometric_hessianDeterminantPolynomial_ne_zero
    (provedDeterminantalTangentOver ℚ) F
  have hex : ∃ x : GeometricPoint 10,
      eval x (hessianDeterminantPolynomial (geometricPolynomial F.polynomial)) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hdet
    apply MvPolynomial.funext
    intro x
    simpa using h x
  obtain ⟨x, hx⟩ := hex
  rw [eval_hessianDeterminantPolynomial] at hx
  have hker : LinearMap.ker (hessian (geometricPolynomial F.polynomial) x).mulVecLin = ⊥ := by
    apply eq_bot_iff.mpr
    intro v hv
    change v = 0
    by_contra hv0
    exact hx (Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv0, hv⟩)
  refine ⟨x, ?_⟩
  have hrn := (hessian (geometricPolynomial F.polynomial) x).mulVecLin.finrank_range_add_finrank_ker
  rw [hker, finrank_bot, add_zero] at hrn
  simpa [Matrix.rank] using hrn

/-- A non-full-rank locus is a proper closed subset of affine ten-space. -/
theorem hessianRankLocus_dimension_le_nine (F : AnisotropicCubic 10)
    (r : ℕ) (hr : r < 10) :
    affineDimension (rankAtMostLocus F.polynomial r) ≤ 9 := by
  obtain ⟨x, hx⟩ := exists_geometric_hessian_full_rank F
  have hproper : rankAtMostLocus F.polynomial r ⊂ (Set.univ : Set (GeometricPoint 10)) := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨Set.subset_univ _, ?_⟩
    intro heq
    have hm : x ∈ rankAtMostLocus F.polynomial r := by rw [heq]; trivial
    change (hessian (geometricPolynomial F.polynomial) x).rank ≤ r at hm
    omega
  have hlt := ReducedStrictDimension.proper_closed _ _ (hessianRankLocus_closed F r)
    algebraicallyClosedSet_univ geometricallyIrreducible_univ hproper
  rw [affineDimension_univ_from_generic_rank Unconditional.genericRankOpen 10] at hlt
  obtain ⟨d, hd⟩ := ReducedComponentDimension.finite_dimension
    (rankAtMostLocus F.polynomial r) ⟨0, origin_mem_hessianRankLocus F r⟩
  rw [hd] at hlt ⊢
  have hdlt : d < 10 := by exact_mod_cast hlt
  exact_mod_cast (show d ≤ 9 by omega)

/-- The n=10 rank-stratum bound required in the manuscript, for all
1 ≤ r ≤ 9 (the proof also gives the bound for r=0). -/
theorem hessianRankLocus_dimension_le_min (F : AnisotropicCubic 10)
    (r : ℕ) (hr : r ≤ 9) :
    affineDimension (rankAtMostLocus F.polynomial r) ≤ ((min (r + 2) 9 : ℕ) : Dimension) := by
  have h₁ := hessianRankLocus_dimension_le_rank_add_two F r
  have h₂ := hessianRankLocus_dimension_le_nine F r (by omega)
  rcases le_total (r + 2) 9 with h | h
  · rwa [min_eq_left h]
  · simpa [min_eq_right h] using h₂

/-- Rank below eight cuts out a proper closed subset of the irreducible
affine cubic, so this on-cubic locus has affine dimension at most eight. -/
theorem onCubic_hessianRankLocus_dimension_le_eight (F : AnisotropicCubic 10)
    (r : ℕ) (hr : r < 8) :
    affineDimension (rankAtMostLocus F.polynomial r ∩ cubicLocus F.polynomial) ≤ 8 := by
  let P := geometricPolynomial F.polynomial
  let A := rankAtMostLocus F.polynomial r ∩ cubicLocus F.polynomial
  have hAclosed : AlgebraicallyClosedSet A := by
    have heq : A = BibleLowRank.onCubicRankLocus P r := by
      ext x
      exact and_comm
    rw [heq]
    exact BibleLowRank.onCubicRankLocus_closed P r
  have hirred : Irreducible P := Unconditional.cubicGeometricIrreducibility F (by norm_num)
  have hproper : A ⊂ polynomialHypersurface P := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨fun _ hx => hx.2, ?_⟩
    intro heq
    obtain ⟨x, hxF, hxrank⟩ := genericHessianRank_attained F
    have hxA : x ∈ A := by rw [heq]; exact hxF
    have hxle : (hessian P x).rank ≤ r := hxA.1
    have hgeneric := genericHessianRank_ge_eight F
    change (hessian P x).rank = genericHessianRank F.polynomial at hxrank
    omega
  have hlt := ReducedStrictDimension.proper_closed A (polynomialHypersurface P)
    hAclosed (polynomialHypersurface_closed P) (polynomialHypersurface_irreducible P hirred)
    hproper
  rw [Unconditional.hypersurfaceDimension.hypersurface P hirred] at hlt
  have hAne : A.Nonempty := ⟨0, origin_mem_hessianRankLocus F r, origin_mem_cubicLocus F⟩
  obtain ⟨d, hd⟩ := ReducedComponentDimension.finite_dimension A hAne
  change affineDimension A ≤ 8
  rw [hd] at hlt ⊢
  have hdlt : d < 9 := by exact_mod_cast hlt
  exact_mod_cast (show d ≤ 8 by omega)

/-- The complete geometric Hessian rank-stratum package needed in ten
variables. The hypotheses are solely that F is a rational homogeneous cubic
whose only rational zero is the origin. -/
theorem hessianRankStrataTen (F : AnisotropicCubic 10) :
    rankAtMostLocus F.polynomial 0 = {0} ∧
    affineDimension (rankAtMostLocus F.polynomial 0) = 0 ∧
    (∀ r : ℕ, 1 ≤ r → r ≤ 9 →
      affineDimension (rankAtMostLocus F.polynomial r) ≤ ((min (r + 2) 9 : ℕ) : Dimension)) ∧
    (∀ r : ℕ, r < 8 →
      affineDimension (rankAtMostLocus F.polynomial r ∩ cubicLocus F.polynomial) ≤ 8) :=
  ⟨(hessianRankZero F).1, (hessianRankZero F).2,
    fun r _ hr => hessianRankLocus_dimension_le_min F r hr,
    fun r hr => onCubic_hessianRankLocus_dimension_le_eight F r hr⟩

end CubicTenVariables.Geometry
