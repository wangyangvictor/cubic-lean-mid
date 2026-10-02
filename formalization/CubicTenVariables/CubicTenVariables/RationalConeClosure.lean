import CubicTenVariables.DavenportHomogeneity
import HessianTheorem11.ReducedGenericImageTangent
import HessianTheorem11.UnconditionalDimensionResults

/-!
# Geometric closure of the rational points of a cone

The rational closure with an adjoined origin is an actual closed geometric
cone. Its rational points are exactly the original rational points together
with zero. Cone stability over the algebraic closure is proved by restricting
each vanishing polynomial to a scalar line and using infinitely many rational
roots; rational dilation stability is not confused with geometric stability.
The construction is not identified with the original geometric cone, and
no claim about its reduction exhausting a finite-field locus is made.
-/

noncomputable section
namespace CubicTenVariables.RationalConeClosure

open MvPolynomial HessianTheorem11 Module

/-- Coordinatewise inclusion of an actual rational vector. -/
def rationalEmbedding {n : ℕ} (x : Fin n → ℚ) : GeometricPoint n :=
  fun i => algebraMap ℚ GeometricField (x i)

@[simp] theorem rationalEmbedding_zero {n : ℕ} :
    rationalEmbedding (0 : Fin n → ℚ) = 0 := by
  ext i
  simp [rationalEmbedding]

theorem rationalEmbedding_injective {n : ℕ} :
    Function.Injective (rationalEmbedding : (Fin n → ℚ) → GeometricPoint n) := by
  intro x y h
  funext i
  exact (algebraMap ℚ GeometricField).injective (congrFun h i)

@[simp] theorem rationalEmbedding_eq_zero_iff {n : ℕ} (x : Fin n → ℚ) :
    rationalEmbedding x = 0 ↔ x = 0 := by
  rw [← rationalEmbedding_zero]
  exact rationalEmbedding_injective.eq_iff

@[simp] theorem rationalEmbedding_smul {n : ℕ} (a : ℚ) (x : Fin n → ℚ) :
    rationalEmbedding (a • x) = (algebraMap ℚ GeometricField a) • rationalEmbedding x := by
  ext i
  simp [rationalEmbedding, smul_eq_mul]

/-- Literal rational points of a geometric point set. -/
def rationalPoints {n : ℕ} (C : Set (GeometricPoint n)) : Set (Fin n → ℚ) :=
  {x | rationalEmbedding x ∈ C}

/-- The source construction: geometric closure of the rational points,
then adjoining the origin even if the original cone is empty. -/
def rationalConeClosure {n : ℕ} (C : Set (GeometricPoint n)) : Set (GeometricPoint n) :=
  geometricClosure (rationalEmbedding '' rationalPoints C) ∪ {0}

/-- Polynomial continuity propagates each rational dilation to the closure. -/
theorem closure_stable_under_rational_smul {n : ℕ} (S : Set (GeometricPoint n))
    (hS : ∀ (a : ℚ), ∀ x ∈ S, (algebraMap ℚ GeometricField a) • x ∈ S)
    (a : ℚ) (x : GeometricPoint n) (hx : x ∈ geometricClosure S) :
    (algebraMap ℚ GeometricField a) • x ∈ geometricClosure S := by
  let P : Fin n → GeometricPolynomial n :=
    fun i => C (algebraMap ℚ GeometricField a) * X i
  have hp : polynomialMap P = fun x : GeometricPoint n =>
      (algebraMap ℚ GeometricField a) • x := by
    funext z i
    simp [P, polynomialMap, Pi.smul_apply, smul_eq_mul]
  have himage : polynomialMap P '' S ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hp]
    exact hS a z hz
  exact geometricClosure_mono himage
    (polynomialMap_image_closure_subset P S ⟨x, hx, congrFun hp x⟩)

/-- Rational dilation stability suffices for full geometric cone stability
after taking geometric Zariski closure. -/
theorem geometricClosure_isAffineCone_of_rational_smul {n : ℕ}
    (S : Set (GeometricPoint n))
    (hS : ∀ (a : ℚ), ∀ x ∈ S, (algebraMap ℚ GeometricField a) • x ∈ S) :
    IsAffineCone (geometricClosure S) := by
  intro a x hx F hF
  let f : Polynomial GeometricField := DavenportHomogeneity.homogeneousScalingHom x F
  have hval (b : ℚ) : f.eval (algebraMap ℚ GeometricField b) = 0 := by
    rw [show f = DavenportHomogeneity.homogeneousScalingHom x F from rfl,
      DavenportHomogeneity.eval_homogeneousScalingHom]
    exact closure_stable_under_rational_smul S hS b x hx F hF
  have hinfinite : Set.Infinite (Set.range (algebraMap ℚ GeometricField)) :=
    Set.infinite_range_of_injective (algebraMap ℚ GeometricField).injective
  have hf : f = 0 := Polynomial.eq_zero_of_infinite_isRoot f (hinfinite.mono (by
    rintro b ⟨c, rfl⟩
    exact hval c))
  have he := congrArg (fun p : Polynomial GeometricField => p.eval a) hf
  simpa only [f, DavenportHomogeneity.eval_homogeneousScalingHom, Polynomial.eval_zero]
    using he

/-- The singleton origin is geometrically closed, including in dimension zero. -/
theorem origin_closed {n : ℕ} : AlgebraicallyClosedSet ({0} : Set (GeometricPoint n)) := by
  apply le_antisymm _ (subset_geometricClosure _)
  intro x hx
  apply Set.mem_singleton_iff.mpr
  ext i
  have hXi : X i ∈ vanishingIdeal GeometricField ({0} : Set (GeometricPoint n)) := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simp [hy]
  simpa only [aeval_X, Pi.zero_apply] using hx (X i) hXi

theorem rationalConeClosure_closed {n : ℕ} (C : Set (GeometricPoint n)) :
    AlgebraicallyClosedSet (rationalConeClosure C) :=
  (algebraicallyClosedSet_geometricClosure _).union origin_closed

@[simp] theorem zero_mem_rationalConeClosure {n : ℕ} (C : Set (GeometricPoint n)) :
    (0 : GeometricPoint n) ∈ rationalConeClosure C := Or.inr rfl

/-- Removing zero before taking the closure and then adjoining it gives
the same construction. This matches the source's nonzero rational normals. -/
theorem rationalConeClosure_eq_nonzero_closure {n : ℕ} (C : Set (GeometricPoint n)) :
    rationalConeClosure C =
      geometricClosure (rationalEmbedding '' {q : Fin n → ℚ |
        rationalEmbedding q ∈ C ∧ q ≠ 0}) ∪ {0} := by
  apply le_antisymm
  · intro x hx
    rcases hx with hx | hx
    · apply geometricClosure_subset_closed _
        ((algebraicallyClosedSet_geometricClosure _).union origin_closed) hx
      rintro _ ⟨q, hq, rfl⟩
      by_cases hzero : q = 0
      · exact Or.inr (by simp [hzero])
      · exact Or.inl (subset_geometricClosure _ ⟨q, ⟨hq, hzero⟩, rfl⟩)
    · exact Or.inr hx
  · intro x hx
    rcases hx with hx | hx
    · apply Or.inl
      exact geometricClosure_mono (Set.image_mono (fun _ hq => hq.1)) hx
    · exact Or.inr hx

/-- The rational closure stays inside the original closed set, apart from
the deliberately adjoined origin. No density hypothesis on C is used. -/
theorem rationalConeClosure_subset {n : ℕ} (C : Set (GeometricPoint n))
    (hC : AlgebraicallyClosedSet C) : rationalConeClosure C ⊆ C ∪ {0} := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (geometricClosure_subset_closed (by
      rintro _ ⟨q, hq, rfl⟩
      exact hq) hC hx)
  · exact Or.inr hx

/-- Full scalar stability, not merely stability under rational units. -/
theorem rationalConeClosure_isAffineCone {n : ℕ} (C : Set (GeometricPoint n))
    (hcone : IsAffineCone C) : IsAffineCone (rationalConeClosure C) := by
  have hrat : ∀ (a : ℚ), ∀ x ∈ rationalEmbedding '' rationalPoints C,
      (algebraMap ℚ GeometricField a) • x ∈ rationalEmbedding '' rationalPoints C := by
    rintro a _ ⟨q, hq, rfl⟩
    refine ⟨a • q, ?_, rationalEmbedding_smul a q⟩
    change rationalEmbedding (a • q) ∈ C
    rw [rationalEmbedding_smul]
    exact hcone _ _ hq
  intro a x hx
  rcases hx with hx | hx
  · exact Or.inl (geometricClosure_isAffineCone_of_rational_smul _ hrat a x hx)
  · rw [Set.mem_singleton_iff] at hx
    simpa [hx] using zero_mem_rationalConeClosure C

/-- The exact rational-point statement. New geometric points may occur,
but no new rational points are added except the origin. -/
theorem rationalEmbedding_mem_iff {n : ℕ} (C : Set (GeometricPoint n))
    (hC : AlgebraicallyClosedSet C) (x : Fin n → ℚ) :
    rationalEmbedding x ∈ rationalConeClosure C ↔ rationalEmbedding x ∈ C ∨ x = 0 := by
  constructor
  · intro hx
    rcases rationalConeClosure_subset C hC hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr ((rationalEmbedding_eq_zero_iff x).mp hx)
  · rintro (hx | rfl)
    · exact Or.inl (subset_geometricClosure _ ⟨x, hx, rfl⟩)
    · simpa using zero_mem_rationalConeClosure C

theorem rationalPoints_rationalConeClosure {n : ℕ} (C : Set (GeometricPoint n))
    (hC : AlgebraicallyClosedSet C) :
    rationalPoints (rationalConeClosure C) = rationalPoints C ∪ {0} := by
  ext x
  exact rationalEmbedding_mem_iff C hC x

/-- The construction is the closure of its displayed rational generators,
with the adjoined zero included among those generators. -/
theorem closure_rational_generators {n : ℕ} (C : Set (GeometricPoint n)) :
    geometricClosure (rationalEmbedding '' (rationalPoints C ∪ {0})) =
      rationalConeClosure C := by
  apply le_antisymm
  · apply geometricClosure_subset_closed _ (rationalConeClosure_closed C)
    rintro _ ⟨q, hq | hq, rfl⟩
    · exact Or.inl (subset_geometricClosure _ ⟨q, hq, rfl⟩)
    · rw [Set.mem_singleton_iff] at hq
      simpa [hq] using zero_mem_rationalConeClosure C
  · intro x hx
    rcases hx with hx | hx
    · exact geometricClosure_mono (Set.image_mono Set.subset_union_left) hx
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact subset_geometricClosure _ ⟨0, Or.inr rfl, rationalEmbedding_zero⟩

/-- Actual rational points are Zariski dense in the constructed set. -/
theorem rationalPoints_dense {n : ℕ} (C : Set (GeometricPoint n))
    (hC : AlgebraicallyClosedSet C) :
    geometricClosure (rationalEmbedding '' rationalPoints (rationalConeClosure C)) =
      rationalConeClosure C := by
  rw [rationalPoints_rationalConeClosure C hC]
  exact closure_rational_generators C

/-- Every nonempty relative open in this rational closure contains an
actual embedded rational vector, not merely a geometric point. -/
theorem exists_rational_point_in_open {n : ℕ} (C : Set (GeometricPoint n))
    (hC : AlgebraicallyClosedSet C) (W : Set (GeometricPoint n))
    (hW : RelativelyOpenSet (rationalConeClosure C) W) (hne : W.Nonempty) :
    ∃ x : Fin n → ℚ, rationalEmbedding x ∈ W := by
  obtain ⟨y, hy, hyW⟩ := ReducedGenericImageTangent.dense_inter_open_nonempty
    (rationalPoints_dense C hC) hW hne
  obtain ⟨x, _, rfl⟩ := hy
  exact ⟨x, hyW⟩

/-- If the open avoids the origin, the selected rational vector is nonzero. -/
theorem exists_nonzero_rational_point_in_open {n : ℕ} (C : Set (GeometricPoint n))
    (hC : AlgebraicallyClosedSet C) (W : Set (GeometricPoint n))
    (hW : RelativelyOpenSet (rationalConeClosure C) W) (hne : W.Nonempty)
    (hzero : (0 : GeometricPoint n) ∉ W) :
    ∃ x : Fin n → ℚ, x ≠ 0 ∧ rationalEmbedding x ∈ W := by
  obtain ⟨x, hx⟩ := exists_rational_point_in_open C hC W hW hne
  exact ⟨x, fun hz => hzero (by simpa [hz] using hx), hx⟩

/-- On an irreducible rational closure, every prescribed nonempty relative
open contains an actual rational smooth point. Smoothness means the equality
of the actual reduced tangent dimension and the actual affine dimension. -/
theorem exists_rational_smooth_point_in_open {n : ℕ} (C : Set (GeometricPoint n))
    (hC : AlgebraicallyClosedSet C)
    (hirred : GeometricallyIrreducible (rationalConeClosure C))
    (W : Set (GeometricPoint n)) (hW : RelativelyOpenSet (rationalConeClosure C) W)
    (hne : W.Nonempty) :
    ∃ x : Fin n → ℚ, rationalEmbedding x ∈ W ∧
      affineDimension (rationalConeClosure C) =
        (finrank GeometricField
          (affineTangentSpace (rationalConeClosure C) (rationalEmbedding x)) : Dimension) := by
  obtain ⟨G⟩ := Unconditional.genericRankOpen.choose (rationalConeClosure C)
    (rationalConeClosure_closed C) hirred (fun _ : Fin 0 => 0)
    (0 : GeometricPoint n →ₗ[GeometricField] Matrix (Fin 0) (Fin 0) GeometricField)
  have hopen := G.isOpen.inter hW
  have hn := ReducedGenericImageTangent.dense_inter_open_nonempty G.dense hW hne
  obtain ⟨x, hxG, hxW⟩ := exists_rational_point_in_open C hC _ hopen hn
  refine ⟨x, hxW, ?_⟩
  rw [G.smooth _ hxG]
  exact G.dimension_base

end CubicTenVariables.RationalConeClosure
