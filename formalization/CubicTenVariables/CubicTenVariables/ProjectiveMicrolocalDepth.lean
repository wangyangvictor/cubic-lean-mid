import CubicTenVariables.Literature.ProjectiveMicrolocalCertificate
import CubicTenVariables.ConormalTerminalComparison

/-! Consequences of the explicit shared microlocal geometric data.
The closedness, conicality, geometric depth codimension and anisotropic
rational codimension gain are proved here; none is part of the literature
certificate. No inhabitant of that certificate is supplied. -/

noncomputable section
namespace CubicTenVariables.ProjectiveMicrolocalDepth
open MvPolynomial HessianTheorem11
open ProjectiveMicrolocalData BihomogeneousIncidenceFamily
open FiniteIncidenceDepth TerminalFiberCoordinates FiberJumpDimension
open RationalConeClosure

variable {n t : ℕ} {F : MvPolynomial (Fin n) ℤ}
  {f : Fin t → Polynomial n n}

/-- Positive-depth loci of the actual common-zero incidence. -/
def depth (f : Fin t → Polynomial n n) (j : ℕ) : Set (GeometricPoint n) :=
  largeFiberParameters (normalProjection n) (geometricIncidence f) j

theorem depth_eq_fiber_dimension (j : ℕ) :
    depth f j = {v | (j : Dimension) ≤ affineDimension (fiber f GeometricField v)} := by
  rw [depth, largeFiberParameters_eq_pointFiber]
  simp only [pointFiber_geometricIncidence]

theorem depth_closed (h : Geometry F f) {j : ℕ} (hj : 0 < j) :
    AlgebraicallyClosedSet (depth f j) := by
  obtain ⟨dx,dv,hdx,hfx,hfv⟩ := h.bihomogeneous
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  exact BihomogeneousIncidenceFamily.depth_closed f dx hfx hdx j

theorem depth_cone (h : Geometry F f) (j : ℕ) : IsAffineCone (depth f j) := by
  obtain ⟨dx,dv,hdx,hfx,hfv⟩ := h.bihomogeneous
  exact BihomogeneousIncidenceFamily.depth_cone f dv hfv j

theorem depth_closure_eq (h : Geometry F f) {j : ℕ} (hj : 0 < j) :
    geometricClosure (depth f j) = depth f j :=
  Set.Subset.antisymm
    (geometricClosure_subset_closed (Set.Subset.refl _) (depth_closed h hj))
    (subset_geometricClosure _)

theorem depth_dimension_le (h : Geometry F f) {j : ℕ} (hj : 0 < j) :
    affineDimension (depth f j) ≤ ((n-j : ℕ) : Dimension) := by
  obtain ⟨c,Y,O,hcover,hY,hiY,hdY,hO,hneO,hconormal⟩ := h.conormalCover
  have hd := FiniteConormalDepth.depth_closure_dimension_le
    (normalProjection n) Y hY hiY hdY hj
  rw [← hcover, ← depth, depth_closure_eq h hj] at hd
  exact hd

theorem geometricPolynomial_integer :
    geometricPolynomial (map (Int.castRingHom ℚ) F) =
      map (Int.castRingHom GeometricField) F := by
  rw [geometricPolynomial, map_map]
  congr 1

theorem fiber_support (h : Geometry F f) (v : GeometricPoint n) :
    fiber f GeometricField v ⊆ cubicLocus (map (Int.castRingHom ℚ) F) := by
  intro x hx
  change eval x (geometricPolynomial (map (Int.castRingHom ℚ) F)) = 0
  rw [geometricPolynomial_integer, eval_map]
  exact (h.incidenceAndGauss.incidence v x hx).1

theorem rational_depth_dimension_le (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) {j : ℕ}
    (hj : 0 < j) (hjn : j < n) :
    affineDimension (rationalConeClosure (depth f j)) ≤
      ((n-(j+1) : ℕ) : Dimension) := by
  obtain ⟨c,Y,O,hcover,hY,hiY,hdY,hO,hneO,hconormal⟩ := h.conormalCover
  have hsupport : ∀ i v, pointFiber (Y i) v ⊆ cubicLocus (map (Int.castRingHom ℚ) F) := by
    intro i v x hx
    apply fiber_support h v
    rw [← pointFiber_geometricIncidence]
    change polynomialMap (fixedNormalSection v) x ∈ geometricIncidence f
    rw [hcover]
    exact Set.mem_iUnion.mpr ⟨i,hx⟩
  have hd := FiniteConormalDepth.rational_depth_closure_dimension_le
    (map (Int.castRingHom ℚ) F) hF Y hY hiY hdY O hO hneO hconormal hsupport hj hjn
  rw [← hcover, ← depth, depth_closure_eq h hj] at hd
  exact hd

theorem depth_antitone {j k : ℕ} (hjk : j ≤ k) : depth f k ⊆ depth f j := by
  rw [depth_eq_fiber_dimension, depth_eq_fiber_dimension]
  intro v hv
  exact (show (j : Dimension) ≤ (k : Dimension) by exact_mod_cast hjk).trans hv

/-- The supplied polynomial incidence is exactly the existing singular
hyperplane-section incidence, after the literal integer coefficient map. -/
theorem incidence_subset_section (h : Geometry F f) :
    ∀ y ∈ geometricIncidence f,
      (polynomialMap (pointProjection n) y, polynomialMap (normalProjection n) y) ∈
        TerminalSectionIncidence.affineSectionSingularIncidence
          (geometricPolynomial (map (Int.castRingHom ℚ) F)) := by
  intro y hy
  have hi := h.incidenceAndGauss.incidence
    (polynomialMap (normalProjection n) y) (polynomialMap (pointProjection n) y) hy
  simpa only [TerminalSectionIncidence.affineSectionSingularIncidence,
    TerminalSectionIncidence.normalMinors, Set.mem_setOf_eq,
    geometricPolynomial_integer, HessianTheorem11.gradient, pderiv_map, eval_map,
    ProjectiveMicrolocalData.gradient] using hi

/-- Outside the already constructed terminal section locus, the same
microlocal fiber has the corresponding dimension bound. -/
theorem fiber_dimension_le_of_not_mem_section (h : Geometry F f)
    (hF : F.IsHomogeneous 3) (r : ℕ) (v : GeometricPoint n)
    (hv : v ∉ TerminalIntegralClosureModels.sectionClosure (map (Int.castRingHom ℚ) F) r) :
    affineDimension (fiber f GeometricField v) ≤ (r : Dimension) := by
  rw [← pointFiber_geometricIncidence]
  exact ConormalTerminalComparison.pointFiber_dimension_le
    (map (Int.castRingHom ℚ) F) (hF.map _) (geometricIncidence f)
    (incidence_subset_section h) r v hv

/-- The precise n=10 geometric and rational codimension gains, on the
same actual loci, without adding either bound to the literature input. -/
theorem ten_depth_bounds {F : MvPolynomial (Fin 10) ℤ}
    {f : Fin t → Polynomial 10 10} (h : Geometry F f)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ 9) :
    AlgebraicallyClosedSet (depth f j) ∧ IsAffineCone (depth f j) ∧
      affineDimension (depth f j) ≤ ((10-j : ℕ) : Dimension) ∧
      affineDimension (rationalConeClosure (depth f j)) ≤ ((9-j : ℕ) : Dimension) := by
  refine ⟨depth_closed h (by omega),depth_cone h j,depth_dimension_le h (by omega),?_⟩
  have hd := rational_depth_dimension_le h hF (j:=j) (by omega) (by omega)
  simpa only [show 10-(j+1) = 9-j by omega] using hd

/-- A single instance of the explicit generic literature certificate yields
all nine positive-depth codimension bounds, with the same finite-field
trace certificate retained for subsequent arithmetic estimates. -/
theorem exists_ten_depth_geometry
    (input : Literature.ProjectiveMicrolocalCertificate)
    (F : MvPolynomial (Fin 10) ℤ) (hne : F ≠ 0) (hhom : F.IsHomogeneous 3)
    (hF : Anisotropic (map (Int.castRingHom ℚ) F)) :
    ∃ (t : ℕ) (f : Fin t → Polynomial 10 10) (N B : ℕ),
      1 ≤ N ∧ 1 ≤ B ∧ Geometry F f ∧ GoodReduction F f N B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ 9 →
        AlgebraicallyClosedSet (depth f j) ∧ IsAffineCone (depth f j) ∧
        affineDimension (depth f j) ≤ ((10-j : ℕ) : Dimension) ∧
        affineDimension (rationalConeClosure (depth f j)) ≤ ((9-j : ℕ) : Dimension) := by
  obtain ⟨t,f,N,B,hN,hB,hgeom,hred⟩ := input 10 3 (by omega) (by omega) F hne hhom
  exact ⟨t,f,N,B,hN,hB,hgeom,hred,fun j hj hjn => ten_depth_bounds hgeom hF j hj hjn⟩

end CubicTenVariables.ProjectiveMicrolocalDepth
