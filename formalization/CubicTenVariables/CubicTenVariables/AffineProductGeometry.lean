import CubicTenVariables.GenericWholeFiberDimension
import CubicTenVariables.TerminalFiberCoordinates

/-!
# Actual two-block affine products

Products of two irreducible geometric affine sets are irreducible by
polynomial specialization and primality of their actual vanishing ideals.
For closed factors, the proved generic whole-fiber theorem and the literal
fixed-normal polynomial inverse give dimension additivity. Consequently a
closed family of at least the sum of its two image dimensions is the entire
product of those image closures. No product-dimension input is assumed.
-/

noncomputable section
namespace CubicTenVariables.AffineProductGeometry
open MvPolynomial HessianTheorem11 Module TerminalFiberCoordinates

/-- The literal pair of point and normal coordinate blocks. -/
def join {n : ℕ} (x v : GeometricPoint n) : GeometricPoint (n+n) :=
  Fin.addCases x v

@[simp] theorem point_join {n : ℕ} (x v : GeometricPoint n) :
    polynomialMap (pointProjection n) (join x v) = x := by
  ext i
  simp only [pointProjection_apply, join, Fin.addCases_left]

@[simp] theorem normal_join {n : ℕ} (x v : GeometricPoint n) :
    polynomialMap (normalProjection n) (join x v) = v := by
  ext i
  simp only [normalProjection_apply, join, Fin.addCases_right]

@[simp] theorem join_projections {n : ℕ} (p : GeometricPoint (n+n)) :
    join (polynomialMap (pointProjection n) p) (polynomialMap (normalProjection n) p) = p := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [join, Fin.addCases_left, Fin.addCases_right,
      pointProjection_apply, normalProjection_apply]

/-- Product as an actual subset of the two-block affine coordinate space. -/
def product {n : ℕ} (C Z : Set (GeometricPoint n)) : Set (GeometricPoint (n+n)) :=
  {p | polynomialMap (pointProjection n) p ∈ C ∧ polynomialMap (normalProjection n) p ∈ Z}

@[simp] theorem join_mem_product {n : ℕ} (C Z : Set (GeometricPoint n))
    (x v : GeometricPoint n) : join x v ∈ product C Z ↔ x ∈ C ∧ v ∈ Z := by
  simp [product]

theorem product_nonempty {n : ℕ} {C Z : Set (GeometricPoint n)}
    (hC : C.Nonempty) (hZ : Z.Nonempty) : (product C Z).Nonempty := by
  obtain ⟨x, hx⟩ := hC
  obtain ⟨v, hv⟩ := hZ
  exact ⟨join x v, (join_mem_product C Z x v).mpr ⟨hx, hv⟩⟩

/-- Closedness uses the actual polynomial coordinate projections. -/
theorem product_closed {n : ℕ} {C Z : Set (GeometricPoint n)}
    (hC : AlgebraicallyClosedSet C) (hZ : AlgebraicallyClosedSet Z) :
    AlgebraicallyClosedSet (product C Z) := by
  have hleft := ReducedGenericImageTangent.closed_polynomial_preimage (pointProjection n) hC
  have hright := ReducedGenericImageTangent.closed_polynomial_preimage (normalProjection n) hZ
  apply Set.Subset.antisymm _ (subset_geometricClosure _)
  intro p hp
  exact ⟨geometricClosure_subset_closed (fun _ h => h.1) hleft hp,
    geometricClosure_subset_closed (fun _ h => h.2) hright hp⟩

def leftSpecialize {n : ℕ} (f : GeometricPolynomial (n+n)) (v : GeometricPoint n) :
    GeometricPolynomial n := aeval (Fin.addCases X (fun i => C (v i))) f

def rightSpecialize {n : ℕ} (f : GeometricPolynomial (n+n)) (x : GeometricPoint n) :
    GeometricPolynomial n := aeval (Fin.addCases (fun i => C (x i)) X) f

@[simp] theorem eval_leftSpecialize {n : ℕ} (f : GeometricPolynomial (n+n))
    (x v : GeometricPoint n) : eval x (leftSpecialize f v) = eval (join x v) f := by
  have he : polynomialMap (Fin.addCases (X : Fin n → GeometricPolynomial n)
      (fun i => C (v i))) x = join x v := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [polynomialMap, join, Fin.addCases_left, Fin.addCases_right, eval_X, eval_C]
  rw [leftSpecialize, ← eval_polynomialMap, he]

@[simp] theorem eval_rightSpecialize {n : ℕ} (f : GeometricPolynomial (n+n))
    (x v : GeometricPoint n) : eval v (rightSpecialize f x) = eval (join x v) f := by
  have he : polynomialMap (Fin.addCases (fun i => C (x i))
      (X : Fin n → GeometricPolynomial n)) v = join x v := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp only [polynomialMap, join, Fin.addCases_left, Fin.addCases_right, eval_X, eval_C]
  rw [rightSpecialize, ← eval_polynomialMap, he]

/-- Irreducibility of the actual product of any two irreducible factors.
The proof tests actual polynomials, rather than assuming an abstract
geometric-product or tensor-product irreducibility theorem. -/
theorem product_irreducible {n : ℕ} (C Z : Set (GeometricPoint n))
    (hiC : GeometricallyIrreducible C) (hiZ : GeometricallyIrreducible Z) :
    GeometricallyIrreducible (product C Z) := by
  classical
  refine ⟨?_, ?_⟩
  · intro htop
    obtain ⟨p, hp⟩ := product_nonempty hiC.nonempty hiZ.nonempty
    have h1 : (1 : GeometricPolynomial (n+n)) ∈ vanishingIdeal GeometricField (product C Z) := by
      rw [htop]
      trivial
    have he := h1 p hp
    simp at he
  · intro f g hfg
    by_cases hf : f ∈ vanishingIdeal GeometricField (product C Z)
    · exact Or.inl hf
    right
    obtain ⟨p, hp, hpf⟩ : ∃ p ∈ product C Z, eval p f ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hf hn
    let x0 := polynomialMap (pointProjection n) p
    let v0 := polynomialMap (normalProjection n) p
    let f0 := leftSpecialize f v0
    have hf0 : f0 ∉ vanishingIdeal GeometricField C := by
      intro hh
      have he := hh x0 hp.1
      change eval x0 f0 = 0 at he
      exact hpf (by simpa only [f0, x0, v0, eval_leftSpecialize, join_projections] using he)
    intro q hq
    let v := polynomialMap (normalProjection n) q
    have hprod : f0 * leftSpecialize g v ∈ vanishingIdeal GeometricField C := by
      intro x hx
      change eval x (f0 * leftSpecialize g v) = 0
      rw [map_mul]
      by_cases hz : eval x f0 = 0
      · rw [hz, zero_mul]
      have hfx : rightSpecialize f x ∉ vanishingIdeal GeometricField Z := by
        intro hh
        have he := hh v0 hp.2
        change eval v0 (rightSpecialize f x) = 0 at he
        exact hz (by simpa only [f0, eval_leftSpecialize, eval_rightSpecialize] using he)
      have he : rightSpecialize f x * rightSpecialize g x ∈ vanishingIdeal GeometricField Z := by
        intro w hw
        change eval w (rightSpecialize f x * rightSpecialize g x) = 0
        rw [map_mul, eval_rightSpecialize, eval_rightSpecialize]
        simpa only [MvPolynomial.aeval_eq_eval, map_mul] using
          hfg (join x w) ((join_mem_product C Z x w).mpr ⟨hx, hw⟩)
      have hgx := (hiZ.mem_or_mem he).resolve_left hfx
      have hgv := hgx v hq.2
      have hzero : eval x (leftSpecialize g v) = 0 := by
        change eval v (rightSpecialize g x) = 0 at hgv
        simpa only [eval_leftSpecialize, eval_rightSpecialize] using hgv
      rw [hzero, mul_zero]
    have hg := (hiC.mem_or_mem hprod).resolve_left hf0
    have he := hg (polynomialMap (pointProjection n) q) hq.1
    change eval (polynomialMap (pointProjection n) q) (leftSpecialize g v) = 0 at he
    change eval q g = 0
    simpa only [v, eval_leftSpecialize, join_projections] using he

/-- The normal projection has exactly the second factor as image whenever
its first factor is nonempty. -/
theorem normal_image_product {n : ℕ} (C Z : Set (GeometricPoint n)) (hC : C.Nonempty) :
    polynomialMap (normalProjection n) '' product C Z = Z := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact hp.2
  · intro v hv
    obtain ⟨x, hx⟩ := hC
    exact ⟨join x v, (join_mem_product C Z x v).mpr ⟨hx, hv⟩, normal_join x v⟩

/-- At a normal in the second factor, the point image of the literal
fixed-normal product fiber is exactly the first factor. -/
theorem point_image_product_fiber {n : ℕ} (C Z : Set (GeometricPoint n))
    (v : GeometricPoint n) (hv : v ∈ Z) :
    polynomialMap (pointProjection n) ''
      {p | p ∈ product C Z ∧ polynomialMap (normalProjection n) p = v} = C := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact hp.1.1
  · intro x hx
    exact ⟨join x v, ⟨(join_mem_product C Z x v).mpr ⟨hx, hv⟩, normal_join x v⟩,
      point_join x v⟩

/-- Dimension additivity for the actual product of closed irreducible
factors, proved from literal fibers and the whole-source theorem. -/
theorem product_dimension {n : ℕ} (C Z : Set (GeometricPoint n))
    (hC : AlgebraicallyClosedSet C) (hiC : GeometricallyIrreducible C)
    (hZ : AlgebraicallyClosedSet Z) (hiZ : GeometricallyIrreducible Z) :
    affineDimension (product C Z) = affineDimension C + affineDimension Z := by
  obtain ⟨c, hc⟩ := ReducedComponentDimension.finite_dimension C hiC.nonempty
  obtain ⟨s, hs⟩ := ReducedComponentDimension.finite_dimension Z hiZ.nonempty
  obtain ⟨d, hd⟩ := ReducedComponentDimension.finite_dimension (product C Z)
    (product_nonempty hiC.nonempty hiZ.nonempty)
  have hprod := product_closed hC hZ
  have hiprod := product_irreducible C Z hiC hiZ
  have himage : geometricClosure (polynomialMap (normalProjection n) '' product C Z) = Z := by
    rw [normal_image_product C Z hiC.nonempty]
    exact hZ
  have hdimImage : affineDimension
      (geometricClosure (polynomialMap (normalProjection n) '' product C Z)) =
        (s : Dimension) := by rw [himage]; exact hs
  have hsd := GenericWholeFiberDimension.image_dimension_le_source
    (normalProjection n) (product C Z) hprod hiprod d s hd hdimImage
  obtain ⟨O, hO, hnO, _, _, hfiber⟩ :=
    GenericWholeFiberDimension.exists_dense_open_whole_fiber_dimension_eq
      (normalProjection n) (product C Z) hprod hiprod d s hd hdimImage
  obtain ⟨v, hv⟩ := hnO
  have hvZ : v ∈ Z := by
    obtain ⟨D, _, hOD⟩ := hO
    exact himage ▸ (hOD ▸ hv).1
  have hf := hfiber v hv
  have hpoint := TerminalFiberCoordinates.fiber_dimension (product C Z) v
  rw [point_image_product_fiber C Z v hvZ, hc, hf] at hpoint
  have he : c = d-s := by exact_mod_cast hpoint
  rw [hd, hc, hs]
  exact_mod_cast (show d = c+s by omega)

/-- A closed family contained in an irreducible product, and with at least
its dimension, must be that entire product. -/
theorem eq_product_of_dimension_ge {n : ℕ}
    (Y : Set (GeometricPoint (n+n))) (C Z : Set (GeometricPoint n))
    (hY : AlgebraicallyClosedSet Y)
    (hC : AlgebraicallyClosedSet C) (hiC : GeometricallyIrreducible C)
    (hZ : AlgebraicallyClosedSet Z) (hiZ : GeometricallyIrreducible Z)
    (hsub : Y ⊆ product C Z)
    (hdim : affineDimension C + affineDimension Z ≤ affineDimension Y) :
    Y = product C Z := by
  by_contra hne
  have hproper : Y ⊂ product C Z := Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  have hlt := ReducedStrictDimension.proper_closed Y (product C Z) hY
    (product_closed hC hZ) (product_irreducible C Z hiC hiZ) hproper
  rw [product_dimension C Z hC hiC hZ hiZ] at hlt
  exact (not_lt_of_ge hdim) hlt

/-- The required family endpoint uses its actual projection closures. -/
theorem eq_product_of_image_dimensions {n : ℕ} (Y : Set (GeometricPoint (n+n)))
    (hY : AlgebraicallyClosedSet Y) (hiY : GeometricallyIrreducible Y)
    (hdim : affineDimension (geometricClosure (polynomialMap (pointProjection n) '' Y)) +
      affineDimension (geometricClosure (polynomialMap (normalProjection n) '' Y)) ≤
        affineDimension Y) :
    Y = product (geometricClosure (polynomialMap (pointProjection n) '' Y))
      (geometricClosure (polynomialMap (normalProjection n) '' Y)) := by
  apply eq_product_of_dimension_ge Y _ _ hY
    (algebraicallyClosedSet_geometricClosure _)
    ((geometricallyIrreducible_closure_iff _).mpr (hiY.polynomialMap_image _))
    (algebraicallyClosedSet_geometricClosure _)
    ((geometricallyIrreducible_closure_iff _).mpr (hiY.polynomialMap_image _))
    _ hdim
  intro p hp
  exact ⟨subset_geometricClosure _ ⟨p, hp, rfl⟩, subset_geometricClosure _ ⟨p, hp, rfl⟩⟩

end CubicTenVariables.AffineProductGeometry
