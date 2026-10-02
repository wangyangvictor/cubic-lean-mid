import CubicTenVariables.AffineProductGeometry
import CubicTenVariables.TerminalIncidenceFamily
import HessianTheorem11.ReducedAffineProductDimension
import HessianTheorem11.UnconditionalResults

/-!
The affine Gauss graph is the actual geometric closure of the polynomial
image (x,a) ↦ (x,a∇F(x)) from the cubic cone times the affine line.
Independent scaling of the two blocks includes the zero point scalar;
that boundary is proved by polynomial closedness, not by dividing by zero.
No projective properness or large-fiber conclusion is assumed here.
-/

noncomputable section
namespace CubicTenVariables.GaussGraph
open MvPolynomial HessianTheorem11 Matrix
open ReducedKernelTangent ReducedAffineProductDimension
open TerminalFiberCoordinates TerminalSectionIncidence AffineProductGeometry

def source {n : ℕ} (F : GeometricPolynomial n) : Set (GeometricPoint (n+1)) :=
  affineCylinder (polynomialHypersurface F) 1

def sourcePair {n : ℕ} (x : GeometricPoint n) (a : GeometricField) :
    GeometricPoint (n+1) := (splitEquiv n 1).symm (x, fun _ => a)

@[simp] theorem base_sourcePair {n : ℕ} (x : GeometricPoint n) (a : GeometricField) :
    baseProjection n 1 (sourcePair x a) = x := by
  change ((splitEquiv n 1) ((splitEquiv n 1).symm (x, fun _ => a))).1 = x
  simp

@[simp] theorem scalar_sourcePair {n : ℕ} (x : GeometricPoint n) (a : GeometricField) :
    fiberProjection n 1 (sourcePair x a) 0 = a := by
  change ((splitEquiv n 1) ((splitEquiv n 1).symm (x, fun _ => a))).2 0 = a
  simp

@[simp] theorem sourcePair_mem {n : ℕ} (F : GeometricPolynomial n)
    (x : GeometricPoint n) (a : GeometricField) :
    sourcePair x a ∈ source F ↔ eval x F = 0 := by
  change eval (baseProjection n 1 (sourcePair x a)) F = 0 ↔ _
  rw [base_sourcePair]

def parametrization {n : ℕ} (F : GeometricPolynomial n) :
    Fin (n+n) → GeometricPolynomial (n+1) :=
  Fin.addCases (linearCoordinatePolynomials (baseProjection n 1))
    (fun i => linearCoordinatePolynomials (fiberProjection n 1) 0 *
      pullback (baseProjection n 1) (pderiv i F))

theorem parametrization_apply {n : ℕ} (F : GeometricPolynomial n)
    (p : GeometricPoint (n+1)) :
    polynomialMap (parametrization F) p = join (baseProjection n 1 p)
      (fiberProjection n 1 p 0 • gradient F (baseProjection n 1 p)) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · simp only [parametrization, polynomialMap, Fin.addCases_left, join]
    exact congrFun (polynomialMap_linearCoordinatePolynomials (baseProjection n 1) p) j
  · simp only [parametrization, polynomialMap, Fin.addCases_right, join, map_mul,
      eval_pullback, Pi.smul_apply, smul_eq_mul, gradient]
    congr 1
    exact congrFun (polynomialMap_linearCoordinatePolynomials (fiberProjection n 1) p) 0

@[simp] theorem parametrization_sourcePair {n : ℕ} (F : GeometricPolynomial n)
    (x : GeometricPoint n) (a : GeometricField) :
    polynomialMap (parametrization F) (sourcePair x a) = join x (a • gradient F x) := by
  rw [parametrization_apply, base_sourcePair, scalar_sourcePair]

@[simp] theorem parametrization_point {n : ℕ} (F : GeometricPolynomial n)
    (p : GeometricPoint (n+1)) :
    polynomialMap (pointProjection n) (polynomialMap (parametrization F) p) =
      baseProjection n 1 p := by rw [parametrization_apply, point_join]

@[simp] theorem parametrization_normal {n : ℕ} (F : GeometricPolynomial n)
    (p : GeometricPoint (n+1)) :
    polynomialMap (normalProjection n) (polynomialMap (parametrization F) p) =
      fiberProjection n 1 p 0 • gradient F (baseProjection n 1 p) := by
  rw [parametrization_apply, normal_join]

def graph {n : ℕ} (F : GeometricPolynomial n) : Set (GeometricPoint (n+n)) :=
  geometricClosure (polynomialMap (parametrization F) '' source F)

theorem image_eq_literal {n : ℕ} (F : GeometricPolynomial n) :
    polynomialMap (parametrization F) '' source F =
      {p | ∃ x : GeometricPoint n, eval x F = 0 ∧
        ∃ a : GeometricField, p = join x (a • gradient F x)} := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨baseProjection n 1 q, hq, fiberProjection n 1 q 0, parametrization_apply F q⟩
  · rintro ⟨x, hx, a, rfl⟩
    exact ⟨sourcePair x a, (sourcePair_mem F x a).mpr hx, parametrization_sourcePair F x a⟩

theorem graph_eq_closure_literal {n : ℕ} (F : GeometricPolynomial n) :
    graph F = geometricClosure {p | ∃ x : GeometricPoint n, eval x F = 0 ∧
      ∃ a : GeometricField, p = join x (a • gradient F x)} := by
  rw [graph, image_eq_literal]

theorem graph_closed {n : ℕ} (F : GeometricPolynomial n) :
    AlgebraicallyClosedSet (graph F) := algebraicallyClosedSet_geometricClosure _

theorem source_closed {n : ℕ} (F : GeometricPolynomial n) :
    AlgebraicallyClosedSet (source F) := by
  have h := ReducedDominantOpen.closed_preimage
    (linearCoordinatePolynomials (baseProjection n 1)) (polynomialHypersurface_closed F)
  have he : polynomialMap (linearCoordinatePolynomials (baseProjection n 1)) =
      baseProjection n 1 := funext (polynomialMap_linearCoordinatePolynomials _)
  rw [he] at h
  exact h

theorem source_irreducible {n : ℕ} (F : GeometricPolynomial n) (hi : Irreducible F) :
    GeometricallyIrreducible (source F) :=
  affineCylinder_irreducible _ (polynomialHypersurface_irreducible F hi)

theorem graph_irreducible {n : ℕ} (F : GeometricPolynomial n) (hi : Irreducible F) :
    GeometricallyIrreducible (graph F) :=
  (geometricallyIrreducible_closure_iff _).mpr
    ((source_irreducible F hi).polynomialMap_image (parametrization F))

theorem graph_mem_incidence {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (p : GeometricPoint (n+n)) (hp : p ∈ graph F) :
    (polynomialMap (pointProjection n) p, polynomialMap (normalProjection n) p) ∈
      affineSectionSingularIncidence F := by
  have hs : polynomialMap (parametrization F) '' source F ⊆
      TerminalIncidenceFamily.incidenceOver F Set.univ := by
    rintro _ ⟨q, hq, rfl⟩
    rw [parametrization_apply]
    change (polynomialMap (pointProjection n) _, polynomialMap (normalProjection n) _) ∈
      affineSectionSingularIncidence F ∧ _
    rw [point_join, normal_join]
    refine ⟨⟨hq, ?_, ?_⟩, Set.mem_univ _⟩
    · rw [smul_dotProduct, dotProduct_comm]
      have he := euler_cubic hF (baseProjection n 1 q)
      change eval (baseProjection n 1 q) F = 0 at hq
      change _ • (∑ i, baseProjection n 1 q i * gradient F (baseProjection n 1 q) i) = 0
      rw [he, hq, mul_zero, smul_zero]
    · intro i j
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  exact (geometricClosure_subset_closed hs
    (TerminalIncidenceFamily.closed_incidenceOver F Set.univ algebraicallyClosedSet_univ) hp).1

theorem gradient_smul {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (a : GeometricField) (x : GeometricPoint n) :
    gradient F (a • x) = a^2 • gradient F x := by
  ext i
  exact SingularNormalEquations.eval_quadratic_smul _ hF.pderiv a x

def blockScaling (n : ℕ) (a b : GeometricField) :
    Fin (n+n) → GeometricPolynomial (n+n) :=
  Fin.addCases (fun i => C a * pointProjection n i) (fun i => C b * normalProjection n i)

theorem blockScaling_apply {n : ℕ} (a b : GeometricField) (p : GeometricPoint (n+n)) :
    polynomialMap (blockScaling n a b) p =
      join (a • polynomialMap (pointProjection n) p) (b • polynomialMap (normalProjection n) p) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [blockScaling, polynomialMap, Fin.addCases_left, Fin.addCases_right,
      join, map_mul, eval_C, Pi.smul_apply, smul_eq_mul]

theorem graph_blockScaling_of_ne_zero {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (a b : GeometricField) (ha : a ≠ 0)
    (p : GeometricPoint (n+n)) (hp : p ∈ graph F) :
    polynomialMap (blockScaling n a b) p ∈ graph F := by
  have hs : polynomialMap (blockScaling n a b) ''
      (polynomialMap (parametrization F) '' source F) ⊆
      polynomialMap (parametrization F) '' source F := by
    rintro _ ⟨q, hq, rfl⟩
    rw [image_eq_literal] at hq ⊢
    obtain ⟨x, hx, c, rfl⟩ := hq
    rw [blockScaling_apply, point_join, normal_join]
    refine ⟨a • x, ?_, b*c/a^2, ?_⟩
    · rw [BibleLowRank.eval_cubic_smul F hF, hx, mul_zero]
    · rw [gradient_smul F hF, smul_smul, smul_smul]
      congr 2
      field_simp
  exact geometricClosure_mono hs
    (polynomialMap_image_closure_subset (blockScaling n a b)
      (polynomialMap (parametrization F) '' source F) ⟨p, hp, rfl⟩)

/-- Independent scalar stability of both coordinate blocks, including the
boundary a=0 by a proved polynomial-closure argument. -/
theorem graph_bicone_smul {n : ℕ} (F : GeometricPolynomial n)
    (hF : F.IsHomogeneous 3) (p : GeometricPoint (n+n)) (hp : p ∈ graph F)
    (a b : GeometricField) :
    join (a • polynomialMap (pointProjection n) p)
      (b • polynomialMap (normalProjection n) p) ∈ graph F := by
  by_cases ha : a ≠ 0
  · simpa only [blockScaling_apply] using graph_blockScaling_of_ne_zero F hF a b ha p hp
  · have haz : a = 0 := not_ne_iff.mp ha
    subst a
    simp only [zero_smul]
    apply closed_contains_missing_line_point (graph F) (graph_closed F)
      (join (polynomialMap (pointProjection n) p) 0)
      (join 0 (b • polynomialMap (normalProjection n) p))
    intro c hc
    have hh := graph_blockScaling_of_ne_zero F hF c b hc p hp
    rw [blockScaling_apply] at hh
    have he : c • join (polynomialMap (pointProjection n) p) 0 +
        join 0 (b • polynomialMap (normalProjection n) p) =
        join (c • polynomialMap (pointProjection n) p)
          (b • polynomialMap (normalProjection n) p) := by
      ext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;>
        simp only [join, Pi.add_apply, Pi.smul_apply, Fin.addCases_left,
          Fin.addCases_right, Pi.zero_apply, smul_zero, zero_add, add_zero]
    exact he ▸ hh

theorem anisotropic_graph_irreducible {n : ℕ} (F : AnisotropicCubic n) (hn : 4 ≤ n) :
    GeometricallyIrreducible (graph (geometricPolynomial F.polynomial)) :=
  graph_irreducible _ (Unconditional.cubicGeometricIrreducibility F hn)

theorem source_dimension {n : ℕ} (F : GeometricPolynomial n) (hi : Irreducible F)
    (hn : 0 < n) : affineDimension (source F) = (n : Dimension) := by
  rw [source, affineCylinder_dimension Unconditional.genericRankOpen _
    (polynomialHypersurface_closed F) (polynomialHypersurface_irreducible F hi),
    Unconditional.hypersurfaceDimension.hypersurface F hi]
  norm_cast
  omega

theorem parametrization_differential_point {n : ℕ} (F : GeometricPolynomial n)
    (p v : GeometricPoint (n+1)) (i : Fin n) :
    polynomialMapDifferential (parametrization F) p v (Fin.castAdd n i) =
      baseProjection n 1 v i := by
  change polynomialDifferential (parametrization F (Fin.castAdd n i)) p v = _
  simp only [parametrization, Fin.addCases_left]
  exact congrFun (LinearMap.congr_fun (differential_linearCoordinates (baseProjection n 1) p) v) i

theorem parametrization_differential_normal {n : ℕ} (F : GeometricPolynomial n)
    (p v : GeometricPoint (n+1)) (i : Fin n) :
    polynomialMapDifferential (parametrization F) p v (Fin.natAdd n i) =
      gradient F (baseProjection n 1 p) i * fiberProjection n 1 v 0 +
        fiberProjection n 1 p 0 *
          polynomialDifferential (pderiv i F) (baseProjection n 1 p) (baseProjection n 1 v) := by
  change polynomialDifferential (parametrization F (Fin.natAdd n i)) p v = _
  simp only [parametrization, Fin.addCases_right, ReducedTangentRank.differential_mul,
    eval_pullback, differential_pullback]
  rw [show polynomialDifferential (linearCoordinatePolynomials (fiberProjection n 1) 0) p v =
      fiberProjection n 1 v 0 from
    congrFun (LinearMap.congr_fun (differential_linearCoordinates (fiberProjection n 1) p) v) 0,
    show eval p (linearCoordinatePolynomials (fiberProjection n 1) 0) =
      fiberProjection n 1 p 0 from
    congrFun (polynomialMap_linearCoordinatePolynomials (fiberProjection n 1) p) 0]
  rfl

/-- The differential of the literal parameterization is injective at
every point whose point coordinate has nonzero gradient. -/
theorem parametrization_differential_injective {n : ℕ} (F : GeometricPolynomial n)
    (p : GeometricPoint (n+1)) (hg : gradient F (baseProjection n 1 p) ≠ 0) :
    Function.Injective (polynomialMapDifferential (parametrization F) p) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro v hv
  have hv0 : polynomialMapDifferential (parametrization F) p v = 0 := hv
  have hb : baseProjection n 1 v = 0 := by
    ext i
    simpa only [parametrization_differential_point, Pi.zero_apply] using congrFun hv0 (Fin.castAdd n i)
  obtain ⟨i, hi⟩ : ∃ i, gradient F (baseProjection n 1 p) i ≠ 0 := by
    by_contra! h
    exact hg (funext h)
  have hs : fiberProjection n 1 v 0 = 0 := by
    have hh := congrFun hv0 (Fin.natAdd n i)
    rw [parametrization_differential_normal, hb, map_zero, mul_zero, add_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left hi
  change v = 0
  apply (splitEquiv n 1).injective
  apply Prod.ext
  · exact hb
  · ext j
    fin_cases j
    exact hs

theorem source_nonsingular_open {n : ℕ} (F : GeometricPolynomial n) :
    RelativelyOpenSet (source F)
      {p | p ∈ source F ∧ gradient F (baseProjection n 1 p) ≠ 0} := by
  refine ⟨baseProjection n 1 ⁻¹' BibleHyperplanes.singularCone F, ?_, ?_⟩
  · have he : polynomialMap (linearCoordinatePolynomials (baseProjection n 1)) =
        baseProjection n 1 := funext (polynomialMap_linearCoordinatePolynomials _)
    simpa only [he] using ReducedDominantOpen.closed_preimage
      (linearCoordinatePolynomials (baseProjection n 1)) (BibleHyperplanes.singularCone_closed F)
  · rfl

/-- The actual affine Gauss bicone has dimension n. The sole geometric
regularity theorem used is the already proved generic differential-rank theorem. -/
theorem graph_dimension {n : ℕ} (F : GeometricPolynomial n) (hF : F.IsHomogeneous 3)
    (hi : Irreducible F) (hn : 0 < n) : affineDimension (graph F) = (n : Dimension) := by
  obtain ⟨x, hx, hg, _, _, _⟩ := exists_smooth_cubic_point_avoiding_polynomial
    ReducedGenericRank.genericMatrixRankInput F hF hi 1
      (fun h => hi.not_isUnit (isUnit_of_dvd_one h))
  have hne : {p | p ∈ source F ∧ gradient F (baseProjection n 1 p) ≠ 0}.Nonempty :=
    ⟨sourcePair x 0, (sourcePair_mem F x 0).mpr hx, by simpa using hg⟩
  obtain ⟨G⟩ := Unconditional.genericRankOpen.choose (source F) (source_closed F)
    (source_irreducible F hi) (parametrization F)
    (0 : GeometricPoint (n+1) →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
  obtain ⟨p, hp, hps⟩ := ReducedGenericImageTangent.dense_inter_open_nonempty
    G.dense (source_nonsingular_open F) hne
  have hinj := parametrization_differential_injective F p hps.2
  have hd := LinearMap.finrank_range_of_inj
    (f := (polynomialMapDifferential (parametrization F) p).domRestrict
      (affineTangentSpace (source F) p)) (hinj.comp Subtype.val_injective)
  rw [G.differential_rank p hp, G.smooth p hp] at hd
  change affineDimension (geometricClosure (polynomialMap (parametrization F) '' source F)) = _
  rw [G.dimension_image, hd, ← G.dimension_base]
  exact source_dimension F hi hn

theorem anisotropic_graph_dimension {n : ℕ} (F : AnisotropicCubic n) (hn : 4 ≤ n) :
    affineDimension (graph (geometricPolynomial F.polynomial)) = (n : Dimension) :=
  graph_dimension _ (geometric_homogeneous F.homogeneous)
    (Unconditional.cubicGeometricIrreducibility F hn) (by omega)

end CubicTenVariables.GaussGraph
