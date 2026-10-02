import CubicTenVariables.RationalConeComponents
import HessianTheorem11.ReducedGaloisSubspace
import HessianTheorem11.KernelGradientSpan

/-!
# Rational descent of actual geometric component tangents

Dense actual rational points force coefficient-conjugation stability of
the reduced vanishing ideal, and hence Galois stability of the point set.
At an actual rational point this gives stability of the embedded tangent
space and its coordinate-pairing annihilator. The proved fixed-field
descent theorem then supplies bases with actual rational coordinates.

Applied to each geometric component of the rational closure, none of these
conclusions assumes rational defining equations or replaces the component.
Smoothness of the chosen point is not needed for tangent descent.
-/

noncomputable section
namespace CubicTenVariables.RationalComponentDescent

open MvPolynomial HessianTheorem11 Module RationalConeClosure RationalConeComponents

/-- The literal coordinatewise action of a rational Galois automorphism. -/
def galoisPoint {n : ℕ} (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (x : GeometricPoint n) : GeometricPoint n := fun i => σ (x i)

@[simp] theorem galoisPoint_rationalEmbedding {n : ℕ}
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (x : Fin n → ℚ) :
    galoisPoint σ (rationalEmbedding x) = rationalEmbedding x := by
  ext i
  exact σ.commutes (x i)

@[simp] theorem galoisPoint_symm_apply {n : ℕ}
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (x : GeometricPoint n) :
    galoisPoint σ.symm (galoisPoint σ x) = x := by
  ext i
  exact σ.symm_apply_apply (x i)

@[simp] theorem galoisPoint_apply_symm {n : ℕ}
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (x : GeometricPoint n) :
    galoisPoint σ (galoisPoint σ.symm x) = x := by
  ext i
  exact σ.apply_symm_apply (x i)

@[simp] theorem coefficientMap_apply_symm {n : ℕ}
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) (f : GeometricPolynomial n) :
    map σ.toRingHom (map σ.symm.toRingHom f) = f := by
  ext d
  simp only [coeff_map]
  exact σ.apply_symm_apply _

/-- Evaluation commutes with the simultaneous coordinate and coefficient
action; this is an identity for the actual multivariate polynomial. -/
theorem eval_coefficientMap {n : ℕ}
    (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (f : GeometricPolynomial n) (x : GeometricPoint n) :
    eval (galoisPoint σ x) (map σ.toRingHom f) = σ (eval x f) := by
  exact (map_eval σ.toRingHom x f).symm

/-- Rational-point density, rather than rational defining equations,
forces the whole reduced vanishing ideal to be stable under conjugation. -/
theorem coefficientMap_mem_vanishingIdeal_of_rational_dense {n : ℕ}
    (Z : Set (GeometricPoint n))
    (hd : geometricClosure (rationalEmbedding '' rationalPoints Z) = Z)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (f : GeometricPolynomial n) (hf : f ∈ vanishingIdeal GeometricField Z) :
    map σ.toRingHom f ∈ vanishingIdeal GeometricField Z := by
  rw [← hd, vanishingIdeal_geometricClosure]
  rintro _ ⟨q, hq, rfl⟩
  change eval (rationalEmbedding q) (map σ.toRingHom f) = 0
  rw [← galoisPoint_rationalEmbedding σ q, eval_coefficientMap]
  exact (map_eq_zero σ).mpr (hf _ hq)

/-- Every point of a rationally dense geometric closed set remains in
that same set under each rational Galois automorphism. -/
theorem galoisPoint_mem_of_rational_dense {n : ℕ}
    (Z : Set (GeometricPoint n))
    (hd : geometricClosure (rationalEmbedding '' rationalPoints Z) = Z)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (x : GeometricPoint n) (hx : x ∈ Z) : galoisPoint σ x ∈ Z := by
  have hclosed : AlgebraicallyClosedSet Z := by
    rw [← hd]
    exact algebraicallyClosedSet_geometricClosure _
  apply hclosed ▸ (show galoisPoint σ x ∈ geometricClosure Z from ?_)
  intro f hf
  have hf' := coefficientMap_mem_vanishingIdeal_of_rational_dense Z hd σ.symm f hf
  have hz := congrArg σ (hf' x hx)
  change σ (eval x (map σ.symm.toRingHom f)) = σ 0 at hz
  rw [map_zero, ← eval_coefficientMap, coefficientMap_apply_symm] at hz
  exact hz

/-- In particular each actual geometric component, not just their union,
is Galois-stable because its actual rational points are dense. -/
theorem galoisPoint_mem_component {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (x : GeometricPoint n) (hx : x ∈ Z) : galoisPoint σ x ∈ Z :=
  galoisPoint_mem_of_rational_dense Z (rationalPoints_dense_in_component C Z hC hZ)
    σ x hx

theorem galoisPoint_image_component {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField) : galoisPoint σ '' Z = Z := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact galoisPoint_mem_component C Z hC hZ σ x hx
  · intro x hx
    exact ⟨galoisPoint σ.symm x,
      galoisPoint_mem_component C Z hC hZ σ.symm x hx, galoisPoint_apply_symm σ x⟩

/-- The differential of the coefficient-conjugated polynomial is the
conjugate of its actual differential under the coordinate action. -/
theorem polynomialDifferential_coefficientMap {n : ℕ}
    (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (f : GeometricPolynomial n) (x v : GeometricPoint n) :
    polynomialDifferential (map σ.toRingHom f) (galoisPoint σ x) (galoisPoint σ v) =
      σ (polynomialDifferential f x v) := by
  simp only [polynomialDifferential_apply, pderiv_map, eval_coefficientMap,
    galoisPoint, map_sum, map_mul]

/-- At any rational ambient point the embedded reduced tangent is
Galois-stable. The point need not be smooth. -/
theorem tangent_galois_stable_of_rational_dense {n : ℕ}
    (Z : Set (GeometricPoint n))
    (hd : geometricClosure (rationalEmbedding '' rationalPoints Z) = Z)
    (q : Fin n → ℚ) (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z (rationalEmbedding q)) :
    galoisPoint σ v ∈ affineTangentSpace Z (rationalEmbedding q) := by
  apply mem_affineTangentSpace.mpr
  intro f hf
  have hf' := coefficientMap_mem_vanishingIdeal_of_rational_dense Z hd σ.symm f hf
  have hz := congrArg σ ((mem_affineTangentSpace.mp hv) _ hf')
  rw [map_zero, ← polynomialDifferential_coefficientMap,
    coefficientMap_apply_symm, galoisPoint_rationalEmbedding] at hz
  exact hz

/-- Coordinate annihilators of Galois-stable subspaces are themselves
Galois-stable, for the literal standard dot-product pairing. -/
theorem orthogonal_galois_stable {n : ℕ}
    (T : Submodule GeometricField (GeometricPoint n))
    (hT : ∀ (σ : GeometricField ≃ₐ[ℚ] GeometricField), ∀ v ∈ T, galoisPoint σ v ∈ T)
    (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (u : GeometricPoint n) (hu : u ∈ coordinatePairing.orthogonal T) :
    galoisPoint σ u ∈ coordinatePairing.orthogonal T := by
  intro v hv
  have hz := congrArg σ (hu (galoisPoint σ.symm v) (hT σ.symm v hv))
  change σ (dotProduct (galoisPoint σ.symm v) u) = σ 0 at hz
  change dotProduct v (galoisPoint σ u) = 0
  simpa only [dotProduct, galoisPoint, map_sum, map_mul, map_zero,
    AlgEquiv.apply_symm_apply] using hz

theorem tangent_galois_stable {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (q : Fin n → ℚ) (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (v : GeometricPoint n) (hv : v ∈ affineTangentSpace Z (rationalEmbedding q)) :
    galoisPoint σ v ∈ affineTangentSpace Z (rationalEmbedding q) :=
  tangent_galois_stable_of_rational_dense Z
    (rationalPoints_dense_in_component C Z hC hZ) q σ v hv

theorem tangent_annihilator_galois_stable {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z)
    (q : Fin n → ℚ) (σ : GeometricField ≃ₐ[ℚ] GeometricField)
    (v : GeometricPoint n)
    (hv : v ∈ coordinatePairing.orthogonal (affineTangentSpace Z (rationalEmbedding q))) :
    galoisPoint σ v ∈ coordinatePairing.orthogonal
      (affineTangentSpace Z (rationalEmbedding q)) :=
  orthogonal_galois_stable _ (tangent_galois_stable C Z hC hZ q) σ v hv

/-- A basis of the actual geometric tangent, each ambient coordinate of
which is the image of a rational number. No rational equations are input. -/
theorem tangent_rational_basis {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z) (q : Fin n → ℚ) :
    ∃ b : Basis (Fin (finrank GeometricField (affineTangentSpace Z (rationalEmbedding q))))
      GeometricField (affineTangentSpace Z (rationalEmbedding q)),
      ∀ i j, ∃ a : ℚ, algebraMap ℚ GeometricField a = (b i).val j :=
  ReducedRationalDescent.invariant_subspace_rational_basis _
    (tangent_galois_stable C Z hC hZ q)

/-- The same actual rational-coordinate descent holds for the tangent
annihilator used by terminal contact and rational restriction arguments. -/
theorem tangent_annihilator_rational_basis {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z) (q : Fin n → ℚ) :
    ∃ b : Basis (Fin (finrank GeometricField
        (coordinatePairing.orthogonal (affineTangentSpace Z (rationalEmbedding q)))))
      GeometricField (coordinatePairing.orthogonal
        (affineTangentSpace Z (rationalEmbedding q))),
      ∀ i j, ∃ a : ℚ, algebraMap ℚ GeometricField a = (b i).val j :=
  ReducedRationalDescent.invariant_subspace_rational_basis _
    (tangent_annihilator_galois_stable C Z hC hZ q)

/-- Rational coordinates in an actual geometric basis give an actual
rational matrix frame, injective both before and after extending scalars. -/
theorem rational_matrix_frame_of_basis {n d : ℕ}
    (T : Submodule GeometricField (GeometricPoint n))
    (b : Basis (Fin d) GeometricField T)
    (hb : ∀ i j, ∃ a : ℚ, algebraMap ℚ GeometricField a = (b i).val j) :
    ∃ B : Matrix (Fin n) (Fin d) ℚ,
      Function.Injective B.mulVec ∧
      Function.Injective (B.map (algebraMap ℚ GeometricField)).mulVec ∧
      LinearMap.range (B.map (algebraMap ℚ GeometricField)).mulVecLin = T := by
  classical
  choose a ha using hb
  let B : Matrix (Fin n) (Fin d) ℚ := fun j i => a i j
  have hcol : (B.map (algebraMap ℚ GeometricField)).col = fun i => (b i).val := by
    funext i j
    exact ha i j
  have hgeom : Function.Injective (B.map (algebraMap ℚ GeometricField)).mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact b.linearIndependent.map' T.subtype (by simp)
  have hQ : Function.Injective B.mulVec := by
    intro x y hxy
    apply rationalEmbedding_injective
    apply hgeom
    ext j
    have he := congrArg (algebraMap ℚ GeometricField) (congrFun hxy j)
    simpa only [RingHom.map_mulVec, rationalEmbedding, Function.comp_apply] using he
  refine ⟨B, hQ, hgeom, ?_⟩
  rw [Matrix.range_mulVecLin, hcol]
  change Submodule.span GeometricField (Set.range (T.subtype ∘ b)) = T
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
    Submodule.range_subtype]

/-- A literal rational frame for the actual geometric tangent. Its number
of columns is exactly the geometric tangent dimension, including zero. -/
theorem tangent_rational_matrix_frame {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z) (q : Fin n → ℚ) :
    ∃ B : Matrix (Fin n)
        (Fin (finrank GeometricField (affineTangentSpace Z (rationalEmbedding q)))) ℚ,
      Function.Injective B.mulVec ∧
      Function.Injective (B.map (algebraMap ℚ GeometricField)).mulVec ∧
      LinearMap.range (B.map (algebraMap ℚ GeometricField)).mulVecLin =
        affineTangentSpace Z (rationalEmbedding q) := by
  obtain ⟨b, hb⟩ := tangent_rational_basis C Z hC hZ q
  exact rational_matrix_frame_of_basis _ b hb

/-- The terminal contact annihilator admits an actual injective rational
matrix whose geometric column space is exactly that annihilator. -/
theorem tangent_annihilator_rational_matrix_frame {n : ℕ}
    (C Z : Set (GeometricPoint n)) (hC : AlgebraicallyClosedSet C)
    (hZ : IsIrreducibleComponent (rationalConeClosure C) Z) (q : Fin n → ℚ) :
    ∃ B : Matrix (Fin n)
        (Fin (finrank GeometricField (coordinatePairing.orthogonal
          (affineTangentSpace Z (rationalEmbedding q))))) ℚ,
      Function.Injective B.mulVec ∧
      Function.Injective (B.map (algebraMap ℚ GeometricField)).mulVec ∧
      LinearMap.range (B.map (algebraMap ℚ GeometricField)).mulVecLin =
        coordinatePairing.orthogonal (affineTangentSpace Z (rationalEmbedding q)) := by
  obtain ⟨b, hb⟩ := tangent_annihilator_rational_basis C Z hC hZ q
  exact rational_matrix_frame_of_basis _ b hb

end CubicTenVariables.RationalComponentDescent
